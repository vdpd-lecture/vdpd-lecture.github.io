method MultipleInsAndOuts(a: int, b: int) returns (x: int, y: int)
  ensures a + b == x
{
  x := a + b;
  y := x + 1;
}


method Allocate1(size: nat) returns (arr: array<int>)
{
  arr := new int[size];
}

method Allocate2(size: int) returns (arr: array<int>)
  requires size >= 0
{
  arr := new int[size];
}

method Allocate3(size: int) returns (arr: array<int>)
{
  if (size >= 0) {
    arr := new int[size];
  } else {
    //... eroare
  }
}


method Aliasing() {
  
  var arr := new int[100];
  var brr := arr;
  arr[7] := 42;
  assert brr[7] == 42;
  
}

predicate Null<T>()
{
  null is array?<T>
}

predicate IsNull<T>(arr: array?)
{
  (arr == null) is bool
}

method exemplu1(a : array?<int>)
{
  assert a == null || a != null;
}

method exemplu2(a : array<int>)
{
  assert (a as array?<int>) != null;
}

// predicate Indexing<T>(arr: array<T>, index: int)
//   requires 0 <= index < arr.Length
// {
//   arr[index] is T
// }

// predicate Length<T>(arr: array<T>) { arr.Length is int }
  
// predicate ToSequence<T>(arr: array<T>)
// {
//   arr[..] is seq<T>
// }



method Example(x: nat, y: nat) returns (z: nat) {
  var t: nat := 0;
  z := 0;
  for i := 0 to x {
    z := z + y;
  }
  z := t;
}


method example3(x: int, y: int) returns (z: int)
  requires x > 0
  requires y > 0
  ensures z == x + y
  ensures z > 0
{
  z := x + y;
}

method Bad(x: nat)
  ensures false
  ensures 2 == 3
  decreases *
{
  Bad(x + 1);
}

method MixedCodeAndProof(x: nat) returns (y: nat)
  requires x > 1
  ensures y > x
{
  y := x + 2;
  assert y == x + 2;
  y := 2 * y;
  assert y == 2 * x + 4;
  y := y - 5;
  assert y == 2 * x - 1; 
}

method MixedCodeAndProof1(x: nat) returns (y: nat, ghost g: int)
  //                                                 ^^^^^^^
  //                                           folosita doar pentru
  //                                           verificare
  //                                           stearsa din cod
  //                                           pe parcursul compilarii
  requires x > 1
  ensures y > x
{
    y := x + 2;
    y := 2 * y;
    g := y + 10;
    y := y - 5;
    assert y > x by {
      assert y == 2 * x - 1;
      assert 2 * x - x > 1;
    }
}

method Times(x: nat, y: nat) returns (z: nat)
  ensures x * y == z
{
  z := 0;
  var i := 0;
  while i < x
    invariant 0 <= i <= x
    invariant i * y == z
  {
    z := z + y;
    i := i + 1;
  }
  // assume 0 <= i <= x;        // i <= x && i <= x ==> i == x
  // assume i * y == z; // x * y == z
  // assume !(i < x); // i >= x
}


predicate Even(b : nat)
{
  b % 2 == 0
}
method asdf(a: nat) returns (b: nat)
  ensures Even(b)
{
  b := 2 * a;
  //assert b % 2 == 0;
  b := b * b;
  //assert b == (2 * a) * (2 * a);
  assert b == 2 * (a * (2 * a)); // pentru demonstratii, sistemul foloseste un SMT solver (Z3)
  // SMT solver reuseste sa demonstreze propozitii din
  // aritmetica liniara a numerelor intregi
  // x, y, z, x + y, 2, 3, ..., x < y, 5 * y,        (NU ESTE PERMIS "x * y")
  // aritmetica neliniara: unde am x * y (nedecidabila)
}


ghost predicate Even'(b : nat)
{
  exists y :: b == 2 * y
}
method asdf'(a: nat) returns (b: nat)
  ensures Even'(b)
{
  b := 2 * a;
  b := b * b;
  assert b == 2 * (a * (2 * a));
}

ghost predicate Even''(b : nat)
{
  exists y :: b == y * 2
}
method asdf''(a: nat) returns (b: nat)
  ensures Even'(b)
{
  b := 2 * a;
  b := b * b;
  assert b == 2 * (a * (2 * a)); // PUZZLE
  //              ^^^^^^^^^^^^^
  //           martor pentru y
}

lemma Aux(x : nat)
  ensures Timesf(x, 0) == 0
{
  if x == 0 {
  } else {
    Aux(x - 1);
  }
}

lemma TimesfCommutative(x: nat, y: nat)
  ensures Timesf(x, y) == Timesf(y, x)
{
  if x == 0 {
    // x == 0
    // TO PROVE: Timesf(0, y) == Timesf(y, 0)
    //    adica: y == 0:        0            == 0 (trivial)
    //           y != 0:        0            == 0 + Timesf(y - 1, 0)
    //           y != 0:        0            == Timesf(y - 1, 0)       (din lema aux)
    //Aux(y);
  } else {
    TimesfCommutative(x - 1, y);
    // Stiu:
    // x != 0
    // Timesf(x - 1, y) = Timesf(y, x - 1)
    // Am de aratat:
    // Timesf(x, y) = Timesf(y, x)
    // ...
  }
}
function Timesf(x : nat, y : nat) : nat
{
  if x == 0 then
    0
  else
    y + Timesf(x - 1, y)
}
method Times2(x: nat, y: nat) returns (z: nat)
  ensures z == Timesf(x, y) // fara aceasta specificatie functionala
{
  z := 0;
  for i := 0 to x
    invariant z == Timesf(i, y)
  {
    z := z + y;
  }
}
method interesant(x : nat, y : nat)
{
  var r1 := Times2(x, y);
  assert r1 == Timesf(x, y);
  var r2 := Times2(y, x);
  assert r2 == Timesf(y, x);
  TimesfCommutative(x, y);
  assert r1 == r2; // ar fi fost imposibil de demonstrat egalitatea de aici
}


type Ref<T> = a: array<T> | a.Length == 1 witness *
// refinement type
// Ref<T> sunt array-uri de dimensiune 1
// au exact 1 element

// pentru tractabilitatea procesului de verificare:

// Conventie: fiecare metoda trebuie sa declare adresele din heap unde
//            poate face actualizari
  
method increment(ref : Ref<int>) // nu intoarce o valoare
  modifies ref                       // trebuie sa declar toate adresele de memorie
                                     // unde am voie sa fac actualizari
  // AVANTAJ: sistemul "stie" ca toate celelalte adrese de memorie nu s-au facut schimbari
  // daca un predicat depinde doar de zonele de memorie unde nu s-au facut schimbari
  // atunci nu mai trebuie "reevaluat" predicatul
  ensures ref[0] == old(ref[0]) + 1
{
  ref[0] := ref[0] + 1;
}

function read(ref : Ref<int>) : int
  reads ref  // functiile/predicatele trebuie sa declare explicit zonele de memorie
             // din heap de unde au voie sa citeasca
{
  ref[0]
}

// Daca am calculat o functie care depinde de niste zone de memorie A
// si apeleze o metoda care modifica doar zonele de memorie B (unde A si B sunt disjuncte)
// nu mai trebuie sa recalculez functia.
method example4(ref1 : Ref<int>, ref2 : Ref<int>)
  requires ref1 != ref2 // asigur ca ref1 si ref2 nu sunt alias-uri
                       // adica ca nu pointeaza spre aceeasi zona de memorie
  modifies ref1
  modifies ref2
{
  var v1 := read(ref1);
  var v2 := read(ref2);
  assert read(ref2) == v2; // am calculat read(ref2), care depinde de zonele de memorie A = { ref2 }.
                           
  increment(ref1);         // apelez o metoda care modifica doar zonele de momorie B = { ref1 }.
  assert read(ref1) == v1 + 1;
  assert read(ref2) == v2; // daca A si B sunt disjuncte, nu mai trebuie sa recalculez read(ref2).
}

// asimetrie:
//   metodele declara ceea ce scriu (au voie sa citeasca tot heapul)
//   functiile declara ceea ce citesc (functiile oricum nu pot scrie in heap)

// zonele de memorie citite de o functie/scrise de o metoda se cheama "frame"
//                                                                    cadru
// functiile declara cadrul de citire (read frame)
// metodele declara cadrul de scriere (write frame)
// daca read frame intersectat cu write frame = multimea vida ==> happy face

function Read(s: seq<Ref<nat>>, idx: nat): nat
  requires idx < |s|
  reads s[idx]
{
  s[idx][0]
}


method Write(s: seq<Ref<nat>>, idx: nat, v: nat)
  requires idx < |s|
  modifies s[idx]
{
  s[idx][0] := v;
}

method TestIncorrect(s: seq<Ref<nat>>) returns (x: nat, y: nat)
  requires |s| > 10
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  //requires s[5] != s[2]
  modifies s
  ensures x == y // s[5] si s[2] ar putea fi aceeasi referinta
{
  x := Read(s, 5);  // read from the object referenced by s[5]
  Write(s, 2, 56);  // write to the object referenced by s[2]
  y := Read(s, 5);  // read from the object referenced by s[5] again
}
