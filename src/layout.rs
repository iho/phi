use crate::lexer::Token;
use logos::Span;

#[derive(Debug, Clone)]
struct LayoutCtx {
    col: usize,
    depth: usize,
    trigger: Token,
}

pub struct LayoutResolver<'a> {
    input: &'a str,
    tokens: Vec<(Token, Span)>,
    pos: usize,
    ctx_stack: Vec<LayoutCtx>,
    brace_depth: usize,
    output_queue: Vec<(Token, Span)>,
    last_token: Option<Token>,
}

impl<'a> LayoutResolver<'a> {
    pub fn new(input: &'a str, tokens: Vec<(Token, Span)>) -> Self {
        Self {
            input,
            tokens,
            pos: 0,
            ctx_stack: Vec::new(),
            brace_depth: 0,
            output_queue: Vec::new(),
            last_token: None,
        }
    }

    fn get_pos(&self, offset: usize) -> (usize, usize) {
        let mut line = 1;
        let mut col = 1;
        for (i, c) in self.input.char_indices() {
            if i == offset {
                break;
            }
            if c == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
        (line, col)
    }

    pub fn iter(self) -> impl Iterator<Item = (usize, Token, usize)> {
        self.resolve().into_iter().map(|(t, s)| (s.start, t, s.end))
    }

    pub fn resolve(self) -> Vec<(Token, Span)> {
        let mut resolver = self;
        let mut result = Vec::new();
        
        while resolver.pos < resolver.tokens.len() || !resolver.output_queue.is_empty() || !resolver.ctx_stack.is_empty() {
            if let Some(token) = resolver.next_token() {
                result.push(token);
            } else {
                break;
            }
        }
        
        result
    }

    fn next_token(&mut self) -> Option<(Token, Span)> {
        if !self.output_queue.is_empty() {
            let (token, span) = self.output_queue.remove(0);
            self.last_token = Some(token.clone());
            return Some((token, span));
        }

        if self.pos >= self.tokens.len() {
            if let Some(_ctx) = self.ctx_stack.pop() {
                return Some((Token::RightBrace, 0..0));
            }
            return None;
        }

        let (token, span) = self.tokens[self.pos].clone();
        let (_line, col) = self.get_pos(span.start);

        if let Token::In = token {
            if let Some(ctx) = self.ctx_stack.last() {
                if let Token::Let = ctx.trigger {
                    self.ctx_stack.pop();
                    return Some((Token::RightBrace, span.start..span.start));
                }
            }
        }

        if let Token::Where = token {
            if let Some(ctx) = self.ctx_stack.last() {
                if matches!(ctx.trigger, Token::Do | Token::Of | Token::Receive) {
                    self.ctx_stack.pop();
                    return Some((Token::RightBrace, span.start..span.start));
                }
            }
        }

        match token {
            Token::RightParen | Token::RightSquare | Token::RightBrace => {
                let new_depth = self.brace_depth.saturating_sub(1);
                if let Some(ctx) = self.ctx_stack.last() {
                    let is_expr_block = match ctx.trigger {
                        Token::Let | Token::Do | Token::Of | Token::Receive => true,
                        _ => false,
                    };
                    if is_expr_block && new_depth < ctx.depth {
                         self.ctx_stack.pop();
                         return Some((Token::RightBrace, span.start..span.start));
                    }
                }
            }
            _ => {}
        }

        if let Some(ctx) = self.ctx_stack.last().cloned() {
            if col < ctx.col && self.brace_depth <= ctx.depth {
                self.ctx_stack.pop();
                return Some((Token::RightBrace, span.start..span.start));
            }

            if col == ctx.col && self.brace_depth == ctx.depth {
                let last_is_trigger = match &self.last_token {
                    Some(Token::Where) | Some(Token::Let) | Some(Token::Do) | Some(Token::Of) | Some(Token::Receive) => true,
                    _ => false,
                };
                let last_is_brace = match &self.last_token {
                    Some(Token::LeftBrace) | Some(Token::Semicolon) => true,
                    _ => false,
                };

                // Specialized 'Else' check: skip semi if it's NOT an 'else instance'
                let is_else_instance = if let Token::Else = token {
                    if self.pos + 1 < self.tokens.len() {
                        matches!(self.tokens[self.pos + 1].0, Token::Instance)
                    } else {
                        false
                    }
                } else {
                    false
                };

                let skip_semi = last_is_trigger || last_is_brace || (match token {
                    Token::In | Token::Then | Token::Of | Token::After | Token::LeftBrace | Token::RightBrace | Token::Where => true,
                    Token::Else if !is_else_instance => true,
                    _ => false,
                });

                if !skip_semi {
                    let semi_span = span.start..span.start;
                    self.last_token = Some(Token::Semicolon);
                    return Some((Token::Semicolon, semi_span));
                }
            }
        }

        self.pos += 1;
        self.last_token = Some(token.clone());

        match token {
            Token::Where | Token::Let | Token::Do | Token::Of | Token::Receive => {
                let (next_col, is_explicit) = if self.pos < self.tokens.len() {
                    let next_token = &self.tokens[self.pos].0;
                    let next_span = &self.tokens[self.pos].1;
                    (self.get_pos(next_span.start).1, matches!(next_token, Token::LeftBrace))
                } else {
                    (col + 1, false)
                };

                self.ctx_stack.push(LayoutCtx {
                    col: next_col,
                    depth: self.brace_depth,
                    trigger: token.clone(),
                });

                if !is_explicit {
                    self.output_queue.push((Token::LeftBrace, span.end..span.end));
                }
                Some((token, span))
            }
            Token::LeftParen | Token::LeftSquare | Token::LeftBrace => {
                self.brace_depth += 1;
                Some((token, span))
            }
            Token::RightParen | Token::RightSquare | Token::RightBrace => {
                self.brace_depth = self.brace_depth.saturating_sub(1);
                Some((token, span))
            }
            _ => Some((token, span)),
        }
    }
}
