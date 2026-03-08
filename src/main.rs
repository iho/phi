use chumsky::Parser;
use logos::Logos;
use ariadne::{Report, ReportKind, Label, Source, Color};
use rayon::prelude::*;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicUsize, Ordering};
use walkdir::WalkDir;
use std::process::Command;
use std::thread;
use std::time::Duration;

mod ast;
mod lexer;
mod parser;
mod layout;
mod type_sys;
mod env;
mod typechecker;
mod beam_writer;
mod asm_writer;
mod ir;
mod regalloc;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let search_paths: Vec<String> = {
        let paths: Vec<String> = args[1..].iter()
            .filter(|a| !a.starts_with("--"))
            .cloned()
            .collect();
        if paths.is_empty() {
            vec!["src/stdlib".to_string(), "src/tests".to_string()]
        } else {
            paths
        }
    };

    // -----------------------------------------------------------------------
    // Pass 1: Parallel parsing
    // -----------------------------------------------------------------------
    println!("--- Batch Parsing ---");

    let phi_paths: Vec<PathBuf> = search_paths.iter().flat_map(|base| {
        WalkDir::new(base)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().map(|s| s == "phi").unwrap_or(false))
            .map(|e| e.path().to_path_buf())
            .collect::<Vec<_>>()
    }).collect();

    let total_count = phi_paths.len();

    // Parse in parallel — each file is independent
    let parse_results: Vec<(PathBuf, Result<ast::Module, ()>)> = phi_paths
        .into_par_iter()
        .map(|path| {
            let result = parse_file(&path);
            (path, result)
        })
        .collect();

    let mut modules: Vec<ast::Module> = Vec::new();
    let mut success_count = 0usize;

    for (path, result) in parse_results {
        match result {
            Ok(m) => { modules.push(m); success_count += 1; }
            Err(_) => eprintln!("FAILED: {:?}", path),
        }
    }

    println!("\nSummary: {}/{} files parsed successfully.", success_count, total_count);

    // -----------------------------------------------------------------------
    // Start FFI generation early to overlap with typechecking and direct BEAM emission
    // -----------------------------------------------------------------------
    println!("\n--- Starting FFI staging in parallel ---");

    let ffi_ok_ctr = Arc::new(AtomicUsize::new(0));
    let ffi_fail_ctr = Arc::new(AtomicUsize::new(0));
    let ffi_total_ctr = Arc::new(AtomicUsize::new(0));

    let ffi_thread = {
        let search_paths = search_paths.clone();
        let ffi_ok_ctr = Arc::clone(&ffi_ok_ctr);
        let ffi_fail_ctr = Arc::clone(&ffi_fail_ctr);
        let ffi_total_ctr = Arc::clone(&ffi_total_ctr);
        thread::spawn(move || {
            let _ = fs::remove_dir_all("ebin");
            let _ = fs::create_dir_all("ebin");

            // -----------------------------------------------------------------------
            // FFI staging and batch compilation (parallel copy/rewrite, single erlc)
            // -----------------------------------------------------------------------
            let ffi_src_dir = Path::new("ebin/ffi_src");
            let _ = fs::remove_dir_all(ffi_src_dir);
            let _ = fs::create_dir_all(ffi_src_dir);

            let ffi_src_dir = ffi_src_dir.to_path_buf();

            // Collect all .hrl files from src/stdlib and copy them into ffi_src_dir/ in parallel.
            let hrl_paths: Vec<PathBuf> = WalkDir::new("src/stdlib")
                .into_iter()
                .filter_map(|e| e.ok())
                .filter(|e| e.path().extension().map(|s| s == "hrl").unwrap_or(false))
                .map(|e| e.path().to_path_buf())
                .collect();

            hrl_paths.par_iter().for_each(|src| {
                if let Some(filename) = src.file_name() {
                    let dest = ffi_src_dir.join(filename);
                    let _ = fs::copy(src, dest);
                }
            });

            // Collect all companion Phi.*.erl paths
            let companion_paths: Vec<PathBuf> = search_paths.iter().flat_map(|base| {
                WalkDir::new(base)
                    .into_iter()
                    .filter_map(|e| e.ok())
                    .filter(|e| e.path().extension().map(|s| s == "erl").unwrap_or(false))
                    .map(|e| e.path().to_path_buf())
                    .collect::<Vec<_>>()
            }).collect();

            // Copy companion .erl files into ffi_src_dir/ root in parallel.
            // Rename Phi.X.erl → Phi.X.FFI.erl so the filename matches the
            // rewritten -module('Phi.X.FFI') declaration (erlc errors on mismatch).
            companion_paths.par_iter().for_each(|src| {
                if let Some(filename) = src.file_name() {
                    let name = filename.to_string_lossy();
                    let dest_name = if name.starts_with("Phi.") && name.ends_with(".erl")
                        && !name.ends_with(".FFI.erl")
                    {
                        format!("{}.FFI.erl", &name[..name.len() - 4])
                    } else {
                        name.into_owned()
                    };
                    let dest = ffi_src_dir.join(&dest_name);
                    let _ = fs::copy(src, dest);
                }
            });

            // Rewrite includes in ffi_src_dir in parallel.
            let rewrite_paths: Vec<PathBuf> = WalkDir::new(&ffi_src_dir)
                .into_iter()
                .filter_map(|e| e.ok())
                .map(|e| e.path().to_path_buf())
                .filter(|path| {
                    path.is_file() && path.extension().map(|s| s == "erl" || s == "hrl").unwrap_or(false)
                })
                .collect();

            rewrite_paths.par_iter().for_each(|path| {
                let content = fs::read_to_string(path).unwrap_or_default();
                let mut lines: Vec<String> = Vec::new();
                let mut changed = false;
                for line in content.lines() {
                    // Rewrite -include paths to flat filenames.
                    if line.trim().starts_with("-include(")
                        && let Some(start) = line.find('"')
                            && let Some(end) = line.rfind('"') {
                                let path_str = &line[start+1..end];
                                if let Some(filename) = Path::new(path_str).file_name() {
                                    let new_include = format!("-include(\"{}\").", filename.to_string_lossy());
                                    if line.trim() != new_include {
                                        lines.push(new_include);
                                        changed = true;
                                        continue;
                                    }
                                }
                            }
                    // Rewrite -module('Phi.X'). → -module('Phi.X.FFI'). so that erlc
                    // produces Phi.X.FFI.beam and does not overwrite phi-compiled Phi.X.beam.
                    // Skip if already has .FFI suffix.
                    if line.trim().starts_with("-module('Phi.") && !line.contains(".FFI'") {
                        let new_line = line.replacen("').", ".FFI').", 1);
                        lines.push(new_line);
                        changed = true;
                        continue;
                    }
                    lines.push(line.to_string());
                }
                if changed {
                    let _ = fs::write(path, lines.join("\n"));
                }
            });

            // Compile all .erl files from ffi_src_dir
            let rewritten_erls: Vec<PathBuf> = WalkDir::new(&ffi_src_dir)
                .into_iter()
                .filter_map(|e| e.ok())
                .filter(|e| e.path().extension().map(|s| s == "erl").unwrap_or(false))
                .map(|e| e.path().to_path_buf())
                .collect();

            ffi_total_ctr.store(rewritten_erls.len(), Ordering::Relaxed);

            if !rewritten_erls.is_empty() {
                let mut erlc = Command::new("erlc");
                erlc
                    .arg("-W0")
                    .arg("-o").arg("ebin")
                    .arg("-I").arg(&ffi_src_dir);

                for erl_path in &rewritten_erls {
                    erlc.arg(erl_path);
                }

                match erlc.output() {
                    Ok(o) if o.status.success() => {
                        ffi_ok_ctr.store(rewritten_erls.len(), Ordering::Relaxed);
                        for erl_path in &rewritten_erls {
                            let _ = fs::remove_file(erl_path);
                        }
                    }
                    Ok(o) => {
                        ffi_fail_ctr.store(rewritten_erls.len(), Ordering::Relaxed);
                        if !o.stderr.is_empty() {
                            eprintln!("ffi erlc failed:\n{}", String::from_utf8_lossy(&o.stderr));
                        }
                    }
                    Err(err) => {
                        ffi_fail_ctr.store(rewritten_erls.len(), Ordering::Relaxed);
                        eprintln!("failed to run erlc for ffi companions: {err}");
                    }
                }
            }
        })
    };

    // -----------------------------------------------------------------------
    // Pass 2: Typechecking (sequential env build, then parallel check)
    // -----------------------------------------------------------------------
    println!("\n--- Typechecking ---");
    let mut current_env = env::Env::new();

    // Sequential: build_env mutates shared state
    for module in &modules {
        typechecker::build_env(module, &mut current_env);
    }

    // Inject implicit Prelude imports (and other stdlib functions)
    // We treat every qualified binding 'Mod.Name' as a potential alias 'Name' -> 'Mod.Name'
    // if Mod is a standard library module.
    let stdlib_aliases: Vec<(String, String)> = current_env.bindings.keys()
        .filter(|k| k.contains('.'))
        .map(|k| {
            let dot = k.rfind('.').unwrap();
            (k[dot+1..].to_string(), k.clone())
        })
        .collect();
    
    for (k, v) in stdlib_aliases {
        // Only inject if it doesn't conflict or if it's from a common module
        if !current_env.term_aliases.contains_key(&k) {
            current_env.term_aliases.insert(k, v);
        }
    }

    let shared_env = Arc::new(current_env);

    // Parallel typecheck — each module gets an independent fresh State; env is Arc<Env> (read-only).
    let tc_results: Vec<_> = modules
        .par_iter()
        .map(|module| typechecker::check_module(module, &shared_env))
        .collect();

    let tc_ok   = tc_results.iter().filter(|r| r.is_ok()).count();
    let tc_fail = tc_results.len() - tc_ok;

    for (module, result) in modules.iter().zip(tc_results.iter()) {
        if let Err(e) = result {
            println!("Type Error in {}: {:?}", module.name, e);
        }
    }
    println!("Typechecking done: {}/{} ok", tc_ok, tc_ok + tc_fail);


    // -----------------------------------------------------------------------
    println!("\n--- Codegen (.phi → .beam directly) ---");

    let direct_ok_ctr = Arc::new(AtomicUsize::new(0));
    let direct_fail_ctr = Arc::new(AtomicUsize::new(0));

    let progress_done = Arc::new(AtomicUsize::new(0));
    let progress_thread = {
        let direct_ok_ctr = Arc::clone(&direct_ok_ctr);
        let direct_fail_ctr = Arc::clone(&direct_fail_ctr);
        let progress_done = Arc::clone(&progress_done);
        thread::spawn(move || {
            while progress_done.load(Ordering::Relaxed) == 0 {
                let d_ok = direct_ok_ctr.load(Ordering::Relaxed);
                let d_fail = direct_fail_ctr.load(Ordering::Relaxed);
                eprint!("\r  [progress] direct: {d_ok} ok / {d_fail} fail");
                let _ = std::io::Write::flush(&mut std::io::stderr());
                thread::sleep(Duration::from_millis(200));
            }
            eprintln!();
        })
    };

    // Prepass: compute actual BEAM arities for all modules (PatBind = 0, Value(binders) = N).
    let beam_arities_raw = beam_writer::compute_beam_arities(&modules);
    for key in ["Phi.Control.Monad.bind", "Phi.Control.Monad.>>=", "Phi.Data.List.replicate", "Phi.Data.List.concat"] {
        if let Some(v) = beam_arities_raw.get(key) {
            eprintln!("[DEBUG beam_arities] {} = {}", key, v);
        } else {
            eprintln!("[DEBUG beam_arities] {} = MISSING", key);
        }
    }
    let beam_arities = Arc::new(beam_arities_raw);

    // Try direct BEAM binary generation in parallel for each module
    let beam_results: Vec<(String, Result<Vec<u8>, beam_writer::BeamGenError>)> = modules
        .par_iter()
        .map(|module| {
            let name = format!("Phi.{}", module.name);
            println!("  [main] Target BEAM: {}.beam (module.name: {})", name, module.name);
            (name, beam_writer::generate_beam(module, &shared_env, &beam_arities))
        })
        .collect();

    let beam_direct_counter = Arc::new(Mutex::new((0usize, 0usize, 0usize))); // (direct_ok, erlc_ok, fail)

    // Count successes/failures (in memory, before any disk writes).
    beam_results.iter().for_each(|(mod_name, gen_res)| {
        match gen_res {
            Ok(_) => {
                direct_ok_ctr.fetch_add(1, Ordering::Relaxed);
                let mut c = beam_direct_counter.lock().unwrap();
                c.0 += 1;
            }
            Err(e) => {
                println!("  [main] Direct BEAM generation failed for {}: {:?}", mod_name, e);
                direct_fail_ctr.fetch_add(1, Ordering::Relaxed);
                let mut c = beam_direct_counter.lock().unwrap();
                c.2 += 1;
            }
        }
    });

    // Wait for FFI thread BEFORE writing phi beams so that phi-compiled modules
    // take priority over any same-named erlc-compiled FFI companions.
    let _ = ffi_thread.join();

    // Write phi-compiled beams after erlc has finished — overwrites FFI stubs.
    beam_results.par_iter().for_each(|(mod_name, gen_res)| {
        if let Ok(beam_bytes) = gen_res {
            let beam_path = format!("ebin/{}.beam", mod_name);
            let _ = fs::write(&beam_path, beam_bytes);
            println!("  Directly emitted: {mod_name}.beam");
        }
    });
    progress_done.store(1, Ordering::Relaxed);
    let _ = progress_thread.join();

    let (direct_ok, _erlc_ok, gen_fail) = {
        let c = beam_direct_counter.lock().unwrap();
        (c.0, c.1, c.2)
    };
    println!("  Direct .beam: {direct_ok} | failed: {gen_fail}");

    // Companion compilation already ran concurrently.
    let ffi_total = ffi_total_ctr.load(Ordering::Relaxed);
    let ffi_ok = ffi_ok_ctr.load(Ordering::Relaxed);
    println!("Erlang Companions Summary: {}/{} files compiled as .FFI.beam successfully.", ffi_ok, ffi_total);

    // -----------------------------------------------------------------------
    // Pass 4: AArch64 ASM codegen (--asm flag or always-on)
    // -----------------------------------------------------------------------
    if args.iter().any(|a| a == "--asm") || std::env::var("PHI_ASM").is_ok() {
        println!("\n--- AArch64 ASM Codegen ---");
        let asm_dir = "easm";
        let _ = fs::create_dir_all(asm_dir);

        // Emit runtime support file once
        let runtime_path = format!("{}/phi_runtime.s", asm_dir);
        let _ = fs::write(&runtime_path, asm_writer::emit_runtime());
        println!("  Emitted: {}", runtime_path);

        let asm_results: Vec<(String, String)> = modules
            .par_iter()
            .map(|module| {
                let name = format!("Phi.{}", module.name);
                let asm = asm_writer::generate_asm(module, &shared_env);
                (name, asm)
            })
            .collect();

        let mut asm_ok = 0usize;
        for (mod_name, asm_text) in &asm_results {
            let path = format!("{}/{}.s", asm_dir, mod_name);
            if fs::write(&path, asm_text).is_ok() {
                println!("  Emitted: {}.s", mod_name);
                asm_ok += 1;
            }
        }
        println!("  ASM: {}/{} modules emitted to {}/", asm_ok, asm_results.len(), asm_dir);
        println!("  Link with: clang -arch arm64 easm/*.s -o phi_out");
    }
}

fn parse_file(path: &Path) -> Result<ast::Module, ()> {
    let input_raw = fs::read_to_string(path).map_err(|e| {
        eprintln!("Error reading file {:?}: {}", path, e);
    })?;
    
    let input = input_raw.replace('\t', "  ");

    let mut lex = lexer::Token::lexer(&input);
    let mut tokens = Vec::new();
    while let Some(res) = lex.next() {
        match res {
            Ok(token) => tokens.push((token, lex.span())),
            Err(_) => {
                eprintln!("Lexer error in {:?} at {:?}", path, lex.span());
                return Err(());
            }
        }
    }

    let resolver = layout::LayoutResolver::new(&input, tokens);
    let token_stream = chumsky::Stream::from_iter(
        0..input.len(),
        resolver.iter().map(|(start, tok, end)| (tok, start..end)),
    );

    match parser::parser().parse(token_stream) {
        Ok(m) => Ok(m),
        Err(errs) => {
            for error in errs {
                let span = error.span();
                let report = Report::build(ReportKind::Error, path.to_string_lossy().to_string(), span.start)
                    .with_message(format!("Unexpected token {:?}", error.found()))
                    .with_label(
                        Label::new((path.to_string_lossy().to_string(), span))
                            .with_message(format!("Unexpected {:?}", error.found()))
                            .with_color(Color::Red),
                    );
                report.finish().print((path.to_string_lossy().to_string(), Source::from(&input))).unwrap();
            }
            Err(())
        }
    }
}

fn regex_capture(pattern: &[u8], content: &str) -> Option<String> {
    use regex::bytes::Regex;
    let re = Regex::new(std::str::from_utf8(pattern).unwrap()).ok()?;
    re.captures(content.as_bytes())
        .and_then(|cap| cap.get(1))
        .map(|m| String::from_utf8_lossy(m.as_bytes()).to_string())
}
