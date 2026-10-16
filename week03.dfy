/*
   f(n) =
   /
   | 0, daca n = 0
   | 1, daca n = 1
   | f(n - 2) + f(n - 1), daca n >= 2
   \
 */
// SPECIFICATIE PENTRU SIRUL LUI FIBONACCI
ghost function fibo_spec(n : nat) : nat
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fibo_spec(n - 2) + fibo_spec(n - 1)
}

// IMPLEMENTAREA PENTRU SIRUL LUI FIBONACCI
method fibo_impl_1(n : nat) returns (r : nat)
  ensures r >= 0
  ensures r == fibo_spec(n)
{
  if n == 0 {
    return 0;
  } else if n == 1 {
    return 1;
  } else {
    // recursiv
    var t1 := fibo_impl_1(n - 2);
    var t2 := fibo_impl_1(n - 1);
    return t1 + t2;
  }
}

/*
   daca specificatia este atat de asemanatoare cu implementarea, atunci pot renunta la "ghost"
 */
function fibo(n : nat) : nat
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fibo(n - 2) + fibo(n - 1)
}
// daca sistemul vede un "function" fara "ghost"
// genereaza doua entitati:
// (1) ghost function fibo(n : nat) : nat { ... }
// (2) method fibo(n : nat) returns (result : nat) ensures result == fibo(n) { ... }


method fibo_impl_2(n : nat) returns (r : nat)
  ensures r == fibo_spec(n)
{
  var a : nat := 0; // ce reprezinta a si b          a = fibo_spec(i - 2), b = fibo_spec(i - 1)
  var b : nat := 1; //                               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  if n == 0 {
    return 0;
  } else if n == 1 {
    return 1;
  } 
  var i := 2;
  while i < n
    // INVARIANTI
    // INVARIANT: este adevarat inainte si dupa fiecare iteratie a corpului buclei while
    invariant 2 <= i <= n
    invariant a == fibo_spec(i - 2)          // de fiecara data cand am un comportament repetitiv
    invariant b == fibo_spec(i - 1)          // (de exemplu: while, for, recursie), am nevoie sa ajut sistemul
  {                                          // cu cativa invarianti
    var temp := a + b;
    a := b;
    b := temp;
    i := i + 1;
  }
  assert i == n;
  return a + b;
}

// INVARIANT INFERENCE: inferenta de invarianti
// dau corpul unui "while"
// rog un calculator sa imi spuna ce invarianti am nevoie


/*
   Pentru fiecare invariant, generam doua "obligatii de verificare":
   1) invariantul are loc la inceput:
   a, b, n : nat
   a = 0
   b = 1
   n != 0
   n != 1
   i = 2
   ------/
   2 <= i <= n && a == fibo_spec(i - 2) && b == fibo_spec(i - 1)
   2) invariantul este mentinut de corpul buclei (invariant preservation/maintainance)
   "daca invariantul este adevarat la inceputul unei iteratii, este adevar si dupa iteratie"
   a, b, n : nat
   2 <= i <= n
   a == fibo_spec(i - 2)
   b == fibo_spec(i - 1)
   a' = b
   b' = a + b
   i' = i + 1
   i < n
   ---------------------/
   2 <= i' <= n && a' == fibo_spec(i' - 2) && b' == fibo_spec(i' - 1)
   
                                              fibo_spec(i - 1)
   2 <= i + 1 <= n && b == fibo_spec(i - 1) && a + b == fibo_spec(i)
                                         fibo_spec(i - 2)

   Pentru ensures se genereaza urmatoarea conditie de verificare:
   a, b, n : nat
   2 <= i <= n (*)
   a == fibo_spec(i - 2)
   b == fibo_spec(i - 1)
   i >= n (**)
   r = a + b
   --------------------/
   r == fibo_spec(n)
   a + b == fibo_spec(i)
   fibo_spec(i - 2) + fibo_spec(i - 1) = fibo_spec(i)    // <-- definitia lui fibo_spec pentru i >= 2
   --------------------//
   Stim ca i = n (din (*) si (**))
   
   
   
 */


/*
   UN LUCRU FUNDAMENTAL PENTRU TRACTABILITATEA PROCESULUI DE VERIFICARE:
   - orice "while" este "uitat" cand avem nevoie sa facem verificarea
   - corpul buclei este "sters" (doar in ceea ce priveste procesul de verificare)
   - nu uita invariantul
 */



/*method test1()
{
  var f0 := fibo_impl_2(0);
  assert f0 == 0;
  var f1 := fibo_impl_2(1);
  assert f1 == 1;
  var f2 := fibo_impl_2(2);
  assert f2 == 1;
  var f3 := fibo_impl_2(3);
  assert f3 == 2;
  var f4 := fibo_impl_2(4);
  assert f4 == 3;
  var f5 := fibo_impl_2(5);
  assert f5 == 5;
}*/





/*
   pentru procesul de verificare al clausei "ensures", sistemul "vede" urmatorul program
method fibo_impl_2(n : nat) returns (r : nat)
  ensures r == fibo_spec(n)
{
  var a : nat;
  var b : nat;
  var i : nat;
  assume i >= n;
  assume 2 <= i <= n;
  assume a == fibo_spec(i - 2);
  assume b == fibo_spec(i - 1);
  return a + b;
}

*/







method double(n : nat) returns (r : nat)
{
  r := n * 2;
}

method use_double(n : nat) returns (r : nat)
  // FAILS: ensures r == 3 * n // nu poate fi demonstrat desi este clar adevarat
  // Atentie! Nu e neaparat ca sistemul sa se descurce sa demonstreze
  // orice lucru adevarat. E posibil sa fie afirmatii adevarate, cum e
  // si cea de aici, pe care sistemul nu reuseste sa le demonstreze.
{
  var temp := double(n);
  return temp + n;
}

// TOT DIN MOTIVE DE TRACTABILITATE A PROCESULUI DE VERIFICARE,
// ORICE APEL DE METODA ESTE "STERS" (pentru verificare)


// method double(n : nat) returns (r : nat)
// {
//   r := n * 2;
// }

// method use_double'(n : nat) returns (r : nat)
//   ensures r == 3 * n
// {
//   var temp : nat; // PENTRU PROCESUL DE VERIFICARE, valoarea lui temp este arbitrara
//   return temp + n;
// }



method double'(n : nat) returns (r : nat)
  ensures r == 2 * n
{
  r := n * 2;
}

method use_double'(n : nat) returns (r : nat)
  ensures r == 3 * n
{
  var temp := double'(n);
  assert temp == 2 * n;
  return temp + n;
}

/*
   PENTRU VERIFICARE, sistemul "vede" urmatorul lucru
method double'(n : nat) returns (r : nat)
  ensures r == 2 * n
{
  r := n * 2;
}

method use_double'(n : nat) returns (r : nat)
  ensures r == 3 * n
{
   var temp : nat;
   assume temp == 2 * n;
   assert temp == 2 * n;
   return temp + n;
}
*/


method ex1(x : int) returns (r : int)
  ensures r >= 0
  ensures r == x * x
{
  return x * x;
}

method ex2(x : int) returns (r : int)
  //ensures r >= 0
  ensures r >= x * x
{
  var temp := ex1(x);
  return temp + 7;
}

/*
   seq
   tipuri algebrice de date (liste, arbori, ...)

   Alte structuri de date functionale pe care nu le-am discutat inca: set, map, iset, imap, multiset, ...
 */

/*
   In Dafny avem array-uri
 */
method min2(x : int, y : int) returns (r : int)
  ensures r <= x && r <= y
{
  if x < y {
    return x - 42;
  } else {
    return y;
  }
}


//             ca un std::vector<int>
method minArray(a : array<int>) returns (r : int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
{
  var i := 0;
  var min := a[i];
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> min <= a[j]
    invariant exists j :: 0 <= j <= i && j < a.Length && min == a[j]
  {
    if (a[i] < min) {
      min := a[i];
    }
    i := i + 1;
  }
  return min;
}

method minArray'(a : array<int>) returns (r : int)
  requires a.Length > 0
  ensures 0 <= r < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[r] <= a[i]
  //ensures exists i :: 0 <= i < a.Length && a[r] == a[i] // i = r e in mod trivial un martor
          // triviala, nu ma ajuta
{
  var i := 0;
  var min_pos := i;
  while i < a.Length
    invariant 0 <= min_pos <= i && min_pos < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[min_pos] <= a[j]
    // invariant exists j :: 0 <= j <= i && j < a.Length && min == a[j]
  {
  if (a[i] < a[min_pos]) {
      min_pos := i;
    }
    i := i + 1;
  }
  return min_pos;
}

method reverseArray(a : array<int>)
  modifies a
  
  // TRY #1:
  //ensures reverseArray(reverseArray(a)) == a
  //        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  //             e o metoda, nu se poate apela intr-o expresie
  
  // TRY #2:
  // ensures forall i :: 0 <= i < a.Length ==> a[i] == a[a.Length - 1 - i]
  // aici scrie ca tabloul este simetric (exemplu: [ 2, 7, 4, 7, 2 ])

  // TRY #3:                   valoarea lui a[i] la sfarsitul metodei
  //                                vvvvv
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
  //                                         ^^^^^^^^^^^^^^^^^^^^^^^^^
  //                                       valoarea expresiei la inceputul metodei
{
  var i := 0;
  var j := a.Length - 1;
  while i <= j
    invariant 0 <= i <= a.Length
    invariant -1 <= j < a.Length
    invariant j == a.Length - 1 - i
    invariant forall k :: (0 <= k < i || j < k < a.Length) ==> a[k] == old(a[a.Length - 1 - k]) // REVENIM, sa vedem de ce nu merge
    invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
    /*
       X Y Z ... A B C
       C Y Z ... A B X
       C B Z ... A Y X
       ^^^         ^^^
       
       */
  {
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
    i := i + 1;
    j := j - 1;
  }
}


method reverseArray'(a : array<int>) returns (a' : array<int>)
  ensures a'.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] == a'[a.Length - i - 1]
{
  a' := new int [ a.Length ];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a'[k] == a[a.Length - k - 1]
  {
    a'[i] := a[a.Length - i - 1];
    i := i + 1;
  }
}
