// BRIEF REMINDER:
// scriem fiecare program de două ori:
// 1) implementare
method computeMax(a : int, b : int) returns (r : int)
  ensures r == maxSpec(a, b) // specificație funcțională
  // eroare: ensures computeMax(3, 4) == 4
  // in specificatii: doar apeluri de functii,
  // nu si apeluri de metode
  
  ensures r >= a && r >= b && (r == a || r == b)
    // specificație relațională
{
  if a > b { // instructiunea "if-else"
    r := a; // alternativ: "return a;"
  } else {
    r := b;
  }
}

// 2) specificație
function maxSpec(a : int, b : int) : int
{
  if a > b then // expresia if-then-else
    a // trebuie sa pun o expresie, nu o instructiune
  else
    b
}

// Pentru a permite scrierea specificațiilor funcționale,
// Dafny conține un sublimbaj funcțional.

// Cursul de azi: partea funcțională din Dafny.

// Esența PF: nu avem efecte secundare.
// Exemple de efecte secundare:
// 1) atribuirea unei noi valori unei variabile
// 2) afișarea unui mesaj pe ecran
// 3) citirea unui input de la tastatură
// 4) ștergerea unui fișier

method cmmdcImpl(a : int, b : int) returns (r : int)
{
  var a' := a;
  var b' := b;
  while a' > 0 && b' > 0
  {
    if a' > b' {
      a' := a' - b';
    } else {
      b' := b' - a';
    }
  }
  if a' > b' {
    r := a';
  } else {
    r := b';
  }
}

function cmmdcSpec(a : int, b : int) : int // program *strict* funcțional
{
  if a > 0 && b > 0 then
    (
    if a > b then
      cmmdcSpec(a - b, b)
    else
      cmmdcSpec(a, b - a)
    )
  else
    (
    if a > b then
      a
    else
      b
    )
}

// functie care calculeaza suma numerelor pana la n
function sumUpTo(n : int) : int
{
  if n <= 0 then
    0
  else
    n + sumUpTo(n - 1)
}

// fibonacci
function fibo(n : int) : int
{
  if n <= 1 then
    n
  else
    fibo(n - 1) + fibo(n - 2)
}

// functie care testeaza daca un numar este prim
  /*
     if (n == 1) {
       return false;
     }
     for (int i = 2; i < n; ++i) {
       if (n % i == 0) {
         return false;
       }
     }
     return true;
     */
function hasDivisors(n : int, lower : int, upper : int) : bool
  // are n divizori in intervalul [lower, upper]?
  requires lower > 0
  decreases upper - lower // valoarea scade strict la fiecare apel recursiv
                          // fara sa scada sub 0
{
  if lower > upper then
    false
  else if n % lower == 0 then
    true
  else
    hasDivisors(n, lower + 1, upper)
}

function isPrime(n : int) : bool
{
  if n <= 1 then
    false
  else
    !hasDivisors(n, 2, n - 1)
}

function max_of_3(a : int, b : int, c : int) : int
{
  var max_2 := maxSpec(a, b); // pot declara variabile
                             // intr-o functie
  maxSpec(max_2, c) // expresia rezultat
}

function nu_merge(a : int, b : int, c : int) : int
{
  var max_2 := maxSpec(a, b); // pot declara variabile
  // intr-o functie
  // max_2 := max_2 + 1; // nu este permisa actualizarea
                         // valorii unei variabile
  maxSpec(max_2, c)
}

/*
   intr-o functie: "return" e o greseala de sintaxa
   "return" este permis doar intr-o metoda
function max_of_2(a : int, b : int) : int
{
  if a > b then
    return a;
  else
    return b;
}
 */

function add_up(a : int, b : int) : int
  requires a >= 0 && b >= 0
{
  // fara sa folosim "+"
  if a == 0 then
    b
  else
    add_up(a - 1, b + 1)
}

// structuri de date funcționale
// secvența
function sumSeq(s : seq<int>) : int
  //            ^^^^^^^^^^^^
  //         "s" este o secventa de numere intregi
{
  if |s| == 0 then
    0
  else // |s| >= 1
    s[0] + sumSeq(s[1..])
}

function doarPare(s : seq<int>) : seq<int> // important: nu se modifica secventa initiala,
                                           // ci se construieste o secventa noua pornind de la cea initiala
{
  if |s| == 0 then
    []
  else if s[0] % 2 == 0 then
    [ s[0] ] + doarPare(s[1..])
  else
    doarPare(s[1..])
}

method test1()
{
  var s : seq<int> := [ 1, 7, 5, 5 ];
  assert s[0] == 1; // indexarea 
  assert |s| == 4; // lungimea
  //       exclusiv
  //         vvvv
  assert s[0..2] == [ 1, 7 ]; // subsecventa
  //      ^^^
  //    inclusiv
  // s[left..right] = subsecventa care incepe pe pozitia left (inclusiv)
  //                  si se termina pe pozitia right (exclusiv)
  // avantaj: right - left = numarul de elemente din subsecventa
  assert s[1..] == [ 7, 5, 5 ];
  assert s[..3] == [ 1, 7, 5 ];
  assert s[..] == [ 1, 7, 5, 5 ];
  // secventele (tipul seq<T>) sunt structuri de date imuabile (engl: immutable)
  // nu este permisa schimbarea unei secvente: eroare: s[1] := 42;

  // fiind intr-o metoda, pot actualiza valoarea variabilei s, punand alta secventa in ea
  s := [ 1, 2, 3 ];

  // actualizare a unei secvente
  s := s[1 := 42];
  assert s == [ 1, 42, 3 ];

  // concatenare
  assert [ 1, 2, 3 ] + [ 7, 6, 5 ] == [ 1, 2, 3, 7, 6, 5 ];

  assert [ 42 ] + [ 1, 2 ] == [ 42, 1, 2 ];
  
  var suma := sumSeq(s);
}

// tipuri de date algebrice generealizeaza tipurile enum
datatype Dow = Mon | Tue | Wed | Thu | Fri | Sat | Sun

function index(dow : Dow) : int
{
  if dow == Mon then
    1
  else if dow == Tue then
    2
  else if dow == Wed then
    3
  else if dow == Thu then
    4
  else if dow == Fri then
    5
  else if dow == Sat then
    6
  else
    7
}

function indexDow(dow : Dow) : int
{
  match dow
    case Mon => 1
    case Tue => 2
    case Wed => 3
    case Thu => 4
    case Fri => 5
    case Sat => 6
    case Sun => 7
}

//           constructurii tipului de date algebric
//              vvvvv   vvvv
datatype List = Empty | Cons(hd : int, tl : List)
//                           ^^        ^^
//                        destructorii tipului de date algebric  

// exemple de lista
// Empty                  []

// Lista 1, 42, 3 se scrie Cons(1, Cons(42, Cons(3, Empty)))

function sumList(l : List) : int
{
  if l == Empty then
    0
  else
    l.hd + sumList(l.tl)
}

method test2()
{
  var l := Cons(1, Cons(42, Cons(3, Empty)));
  assert sumList(l) == 46;
  assert convert(l) == [ 1, 42, 3 ];
}

function convert(l : List) : seq<int>
{
  if l.Empty? then
    []
  else
    [ l.hd ] + convert(l.tl)
}

function convert'(s : seq<int>) : List
{
  if s == [] then
    Empty
  else
    Cons(s[0], convert'(s[1..]))
}


datatype Maybe = Nothing | Just(n : nat)

// Varianta 1 nu functioneaza deoarece y ar putea fi 0
// function impartire(x : nat, y : nat) : nat
// {
//   x / y
// }

// Varianta 2
function impartire'(x : nat, y : nat) : nat
  requires y != 0
{
  x / y
}

// Varianta 3
function impartire''(x : nat, y : nat) : Maybe
{
  if y == 0 then
    Nothing
  else
    Just(x / y)
}



datatype ABC = Vid | Nod(info : int, left : ABC, right : ABC)

  /*
     7
    / \
   3   10
  / \
 1   4 

Nod(7, Nod(3, Nod(1, Vid, Vid), Nod(4, Vid, Vid)), Nod(10, Vid, Vid))
   */

function search(arbore : ABC, x : int) : bool
  // pp ca arbore este arbore binar de cautare
{
  if arbore == Vid then
    false
  else if arbore.info == x then
    true
  else if x < arbore.info then
    search(arbore.left, x)
  else
    search(arbore.right, x)
}

method test3()
{
  var arbore := Nod(7, Nod(3, Nod(1, Vid, Vid), Nod(4, Vid, Vid)), Nod(10, Vid, Vid));
  var find1 := search(arbore, 7); // pot apela o functie dintr-o metoda (!!!)
  var find2 := search(arbore, 20);
  assert find1;
  assert !find2;
}

/*
method simple() returns (r : int)
{
  r := 7;
}

function asdf() : int
{
   simple() // Eroare: nu pot apela o metoda dintr-o functie
}
 */

// TOATE functiile de mai sus sunt executabile (pot fi apelate dintr-o metoda)

// In Dafny, spre deosebire de alte limbaje functionale,
// pot scrie functii care nu sunt (neaparat) executabile.

// Astfel de functii (neexecutabile) sunt numite functii-fantoma.
// Engleza: ghost functions

ghost function isPrime'(n : nat) : bool
{
  // ! exists d :: 2 <= d < n && n % d == 0
  ! exists d :: 2 <= d < n && d != 0 && n % d == 0
}

method test4()
{
  var result := isPrime'(7);
  assert result;
}

function sorted(s : seq<int>) : bool
{
  if |s| <= 1 then
    true
  else
    s[0] < s[1] && sorted(s[1..])
}

ghost function sorted'(s : seq<int>) : bool
{
  forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

ghost function sorted''(s : seq<int>) : bool
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}


method binarySearch(x : int, a : array<int>) returns (pos : int)
  // preconditie
  requires sorted''(a[..])
  // postconditie
  ensures pos >= -1
  ensures pos < a.Length
  ensures pos != -1 ==> a[pos] == x
  ensures pos == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
  var left : int := 0;
  var right : int := a.Length - 1;
  while (left <= right)
    invariant 0 <= left <= a.Length
    invariant -1 <= right < a.Length
    invariant forall i :: 0 <= i < left ==> a[i] < x
    invariant forall i :: right < i < a.Length ==> a[i] > x
  {
    var middle := (left + right) / 2;
    if (a[middle] == x) {
      return middle;
    } else if (a[middle] < x) {
      left := middle + 1;
    } else {
      right := middle - 1;
    }
  }
  return -1;
}


// Functiile ghost sunt utile in partea de specificatie
// (chiar daca nu stiu sa le execut, pot face demonstratii despre ele)


// Functiile care intorc bool se numesc predicate.
ghost predicate sorted'''(s : seq<int>) // nu mai am nevoie sa scriu ca intoarce "bool"
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

function indexOfPositive(s : seq<int>) : int
  requires exists i :: 0 <= i < |s| && s[i] > 0
  ensures 0 <= indexOfPositive(s) < |s| && s[indexOfPositive(s)] > 0
{
  if |s| == 0 then
    -1
  else if s[0] > 0 then
    0
  else
    1 + indexOfPositive(s[1..])
}

ghost function indexOfPositive'(s : seq<int>) : int
  requires exists i :: 0 <= i < |s| && s[i] > 0
  ensures 0 <= indexOfPositive'(s) < |s| && s[indexOfPositive'(s)] > 0
{
  var i :| 0 <= i < |s| && s[i] > 0; // fie i astfel incat 0 <= i < |s| && s[i] > 0
  i
}
