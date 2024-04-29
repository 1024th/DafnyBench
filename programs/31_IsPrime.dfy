method IsPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> forall i: int :: 2 <= i < n ==> n % i != 0
{
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant forall j: int :: 2 <= j < i ==> n % j != 0
  {
    if n % i == 0 {
      return false;
    }
    i := i + 1;
  }
  return true;
}
