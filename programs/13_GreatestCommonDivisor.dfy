// Functional GCD
// No specification now!
function gcd(m: int, n: int): int
  requires m > 0
  requires n > 0
  decreases m+n
{
  if (n==m) then n
  else if (m>n) then gcd(m-n, n)
  else gcd(m, n-m)
}
