
-define(Nothing, {'Nothing'}).

-define(Just(A), {'Just', A}).

-type maybe_t(A) :: {'Nothing'} | {'Just', A}.
