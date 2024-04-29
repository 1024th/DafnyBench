// HumanEval/20
// From a supplied list of numbers (of length at least two) select and return two that are the closest to each
// other and return them in order (smaller number, larger number).

function abs(x: real): real
{
  if x < 0.0 then
    -x
  else
    x
}

method FindClosestElements(numbers: seq<real>) returns (a: real, b: real)
  requires |numbers| >= 2
  ensures a <= b
  ensures exists i, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && a == numbers[i] && b == numbers[j]
  ensures forall i, j: int :: 0 <= i < j < |numbers| ==> abs(numbers[i] - numbers[j]) >= abs(a - b)
{
  ghost var i_ans := 0;
  ghost var j_ans := 1;
  a := numbers[0];
  b := numbers[1];
  var minDiff := abs(a - b);
  assert(0 <= i_ans < j_ans < |numbers| && a == numbers[i_ans] && b == numbers[j_ans]);

  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant minDiff == abs(a - b)
    invariant 0 <= i_ans < j_ans < |numbers| && a == numbers[i_ans] && b == numbers[j_ans]
    invariant forall i', j': int :: (0 <= i' < i && i' < j' < |numbers|) ==> abs(numbers[i'] - numbers[j']) >= minDiff
  {
    var j := i+1;
    while j < |numbers|
      invariant 0 <= i < j <= |numbers|
      invariant minDiff == abs(a - b)
      invariant 0 <= i_ans < j_ans < |numbers| && a == numbers[i_ans] && b == numbers[j_ans]
      invariant forall i', j': int :: (0 <= i' < i && i' < j' < |numbers|) ==> abs(numbers[i'] - numbers[j']) >= minDiff
      invariant forall j': int :: (i < j' < j) ==> abs(numbers[i] - numbers[j']) >= minDiff
    {
      if abs(numbers[i] - numbers[j]) < minDiff {
        i_ans := i;
        j_ans := j;
        a := numbers[i];
        b := numbers[j];
        minDiff := abs(a - b);
        assert(0 <= i_ans < j_ans < |numbers| && a == numbers[i_ans] && b == numbers[j_ans]);
      }
      j := j + 1;
      assert(forall i', j': int :: (0 <= i' < i && i' < j' < |numbers|) ==> abs(numbers[i'] - numbers[j']) >= minDiff);
      assert(forall j': int :: (i < j' < j) ==> abs(numbers[i] - numbers[j']) >= minDiff);
    }
    i := i + 1;
  }
  assert(0 <= i_ans < j_ans < |numbers| && a == numbers[i_ans] && b == numbers[j_ans]);
  assert(exists i, j: int :: 0 <= i < j < |numbers| && a == numbers[i] && b == numbers[j]);

  // Ensure that a <= b
  if a > b {
    var tmp := a;
    a := b;
    b := tmp;
  }
}