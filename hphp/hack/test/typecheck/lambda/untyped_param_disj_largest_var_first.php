<?hh

// The disjunction `#2 <: dynamic || #4 <: dynamic || #2 <: int || #4 <: int`
// (from `(#4 & #2) <: ~int`) is tried from the largest type variable: OCaml's
// `Tvid.Map.elements` lists the bindings in decreasing order of the keys.
function f(vec<string> $users, vec<string> $missing): void {
  $uc = ($a) ==> $missing[$a] ?? $users[$a];
  $uc(0);
}
