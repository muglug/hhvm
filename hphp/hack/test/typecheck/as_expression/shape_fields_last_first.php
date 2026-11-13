<?hh

// The fields are visited in decreasing order of their names
// (`TShapeMap.values`), and the first invalid one is reported.
function g(mixed $x): void {
  $x as shape('a' => (function(): void), 'b' => vec<int>, 'c' => void);
}
