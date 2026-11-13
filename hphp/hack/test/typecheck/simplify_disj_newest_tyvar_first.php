<?hh

// The disjunction `string <: #18 & int <: #18 | Ok<int|string> <: #3
// | Ok<int|string> <: #0` met at `$res->getError()` is tried with the
// disjuncts on the newest type variable first (`simplify_disj` lists
// the bounds by `Tvid.Map.elements`, in decreasing order): the bound goes
// to the variable of `$b`, and `$a` stays a `dict<int, Ok<int>>`.

final class Ok<+T> {
  public function getError(): string {
    return "";
  }
}

function d_merge<Tk as arraykey, Tv>(
  dict<Tk, Tv> $first,
  dict<Tk, Tv> $rest,
): dict<Tk, Tv> {
  return dict[];
}
function d_map<Tk as arraykey, Tv1>(
  dict<Tk, Tv1> $traversable,
  (function(Tv1): string) $value_func,
): void {}
function mlc<Tv2>((function(int): Tv2) $f): dict<int, Tv2> {
  return dict[];
}
function create(): Ok<int> {
  throw new Exception();
}
function fsr(): Ok<string> {
  throw new Exception();
}
function take(dict<int, Ok<int>> $x): void {}

function before(): void {
  $a = mlc(($ts) ==> create());
  $b = mlc(($ts) ==> fsr());
  d_map(d_merge($a, $b), $res ==> $res->getError());
  take($a);
}
