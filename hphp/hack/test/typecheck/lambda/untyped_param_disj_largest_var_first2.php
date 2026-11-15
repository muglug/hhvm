<?hh

function mp<T1, T2>(Traversable<T1> $t, (function(T1): T2) $f): vec<T2> {
  return vec[];
}

function f(): void {
  $t = ($hashes) ==> {
    mp($hashes, $h ==> $h as int);
  };
  $t(vec[1]);
}
