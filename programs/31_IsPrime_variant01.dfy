method IsPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> forall i: int :: 2 <= i < n ==> n % i != 0
{
  var i := 2;
  while i * i <= n
    invariant 2 <= i <= n
    invariant forall j: int :: 2 <= j < i ==> n % j != 0
  {
    if n % i == 0 {
      assert 2 <= i < n && n % i == 0;
      return false;
    }
    i := i + 1;
  }
  assert forall j: int :: 2 <= j < i ==> n % j != 0;
  assert i * i > n;
  forall j: int | 2 <= j && j * j <= n ensures j < i {
    assert j * j < i * i;
    if j >= i {  // Prove by contradiction
      SquareMono(i, j);
      assert j * j >= i * i;
      assert false;
    }
  }
  assert forall i: int :: 2 <= i && i * i <= n ==> n % i != 0;
  PrimeSqrt(n);
  assert forall i: int :: 2 <= i < n ==> n % i != 0;
  return true;
}

lemma PrimeSqrt(n: int)
  requires n >= 2
  requires p: (forall i: int :: 2 <= i && i * i <= n ==> n % i != 0)
  ensures (forall i: int :: 2 <= i < n ==> n % i != 0)
{
  forall i: int | 2 <= i < n
    ensures n % i != 0

  {
    if i * i <= n {
      assert n % i != 0 by { reveal p; }
    } else {  // Prove by contradiction
      assert i * i > n;
      if n % i == 0 {
        var j := n / i;
        assert i * j == n;
        assert n % j == 0 by { LemmaProductModulus(i, j); }
        assert j * j < n by {
          assert j * i == n;
          assert j * i < i * i;
          assert j < i by { LtRightDiv(j, i, i); }
          LtLeftTimes(j, i, j);
          assert j * j < j * i;
        }
        assert 2 <= j && j * j <= n;
        assert n % j != 0 by {
          reveal p;
        }
        assert false;
      }
    }
  }
}

lemma LtRightDiv(x: int, y: int, c: int)
  requires c > 0
  requires x * c < y * c
  ensures x < y
{}

lemma LtRightTimes(x: int, y: int, r: int)
  requires r > 0
  requires x < y
  ensures x * r < y * r
{}

lemma LtLeftTimes(x: int, y: int, l: int)
  requires l > 0
  requires x < y
  ensures l * x < l * y
{}

lemma LeRightTimes(x: int, y: int, r: int)
  requires r > 0
  requires x <= y
  ensures x * r <= y * r
{}

lemma LeLeftTimes(x: int, y: int, l: int)
  requires l > 0
  requires x <= y
  ensures l * x <= l * y
{}

lemma SquareMono(a: int, b: int)
  requires a >= 1 && b >= 1
  requires a <= b
  ensures a * a <= b * b
{
  calc {
    a * a;
  <= { LeRightTimes(a, b, a); }
    b * a;
  <= { LeLeftTimes(a, b, b); }
    b * b;
  }
}

lemma SquareStrictMono(a: int, b: int)
  requires a >= 1 && b >= 1
  requires a < b
  ensures a * a < b * b
{
  calc {
    a * a;
  < { LtRightTimes(a, b, a); }
    b * a;
  < { LtLeftTimes(a, b, b); }
    b * b;
  }
}

lemma LemmaProductModulus(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures a * b % b == 0
{
  var x: int := a * b / b;
  assert a * b == x * b + (a * b % b);
  assert a < x + 1 by {
    assert (a * b % b) < b;
    assert a*b < x*b + b;
    assert x*b + b == (x + 1) * b;
    assert a*b < (x + 1) * b;
  }
  assert a >= x by {
    assert 0 <= (a * b % b);
    assert a*b >= x*b;
    if a < x {
      assert a*b < x*b by { LtRightTimes(a, x, b); }
      assert false;
    }
  }
  assert a == x;
  assert a * b % b == 0;
}
