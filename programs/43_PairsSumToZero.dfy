method PairsSumToZero(l: seq<int>) returns (r: bool)
  ensures r <==> (exists i, j :: 0 <= i < j < |l| && l[i] + l[j] == 0)
{
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall i', j :: 0 <= i' < i && i' < j < |l| ==> l[i'] + l[j] != 0
  {
    var j := i + 1;
    while j < |l|
      invariant i < j <= |l|
      invariant forall j' :: i < j' < j ==> l[i] + l[j'] != 0
    {
      if l[i] + l[j] == 0 {
        return true;
      }
      j := j + 1;
    }
    assert forall j :: i < j < |l| ==> l[i] + l[j] != 0;
    i := i + 1;
  }
  assert forall i, j :: 0 <= i < j < |l| ==> l[i] + l[j] != 0;
  return false;
}
