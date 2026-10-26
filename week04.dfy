// METODE DE DEMONSTRARE
  /*

bool sorted(int a[], int n)
{
   for (int i = 0; i < n - 1; ++i) {
     if (a[i + 1] <= a[i]) {
       return false;
     }
   }
   return true;
}

bool sorted(int a[], int n)
{
   for (int i = 0; i < n; ++i) {
     for (int j = i + 1; j < n; ++j) {
        if (a[i] >= a[j]) {
         return false;
       }
     }
   }
   return true;
}
   
   
   */
  
method binarySearch(a : array<int>, x : int) returns (pos : int)
  requires sorted2(a)
  // requires forall i :: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1]  // DE CE SISTEMUL ESUEAZA CU ACEASTA
                                                                // EXPRIMARE A PRECONDITIEI?
  // requires forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]       
  ensures pos == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
  ensures pos != -1 ==> 0 <= pos < a.Length && a[pos] == x
{
  var left := 0;
  var right := a.Length - 1;
  while left <= right
    invariant 0 <= left <= a.Length
    invariant -1 <= right < a.Length
    invariant forall i :: 0 <= i < left ==> a[i] < x           // 
    invariant forall i :: right < i < a.Length ==> a[i] > x   // 
  {
    var mid := (left + right) / 2;
    if x == a[mid] {
      return mid;
    } else if (x < a[mid]) {
      right := mid - 1;
    } else {
      left := mid + 1;
    }
  }
  return -1;
}

// IN CONTINUARE, VREAU SA INTELEGEM DE CE SISTEMUL REUSESTE SA DEMONSTREZE cu sorted2,
// dar nu cu sorted1.

predicate sorted1(a : array<int>)
  reads a
{
  forall i :: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1]
}

method experiment1(a : array<int>)
  requires sorted1(a)
  requires a.Length > 10
{
  // STIU
  //   forall i :: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1] (*)
  //   a.Length > 10
  // VREAU SA ARAT
  //   a[0] < a[1]
  // Ar fi util sa aleg i = 0 in (*).
  // Am 0 <= i = 0 < 9 < a.Length - 1, si deci a[0] < a[0 + 1],
  // adica a[0] < a[1], ceea ce voiam sa arat.
  assert a[0] < a[1];
}

method experiment2(a : array<int>)
  requires sorted1(a)
  requires a.Length > 10
{
  // STIU
  //   forall i :: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1] (*)
  //   a.Length > 10
  // VREAU SA ARAT
  //   a[0] < a[5]
  // Ar fi util sa aleg i = 0 (?), as obtine a[0] < a[1].
  //                    i = 4 (?), as obtine a[4] < a[5];
  // FAILS: assert a[0] < a[5];
}

method experiment2'(a : array<int>)
  requires sorted1(a)
  requires a.Length > 10
{
  // STIU
  //   forall i :: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1] (*)
  //   a.Length > 10
  // VREAU SA ARAT
  //   a[0] < a[5]
  // Ar fi util sa aleg i = 0 (?), as obtine a[0] < a[1].
  //                    i = 4 (?), as obtine a[4] < a[5];
  assert a[0] < a[1];
  assert a[1] < a[2];
  assert a[2] < a[3];
  assert a[3] < a[4];
  assert a[4] < a[5];
  assert a[0] < a[5];
}


predicate sorted2(a : array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
}

method experiment3(a : array<int>)
  requires sorted2(a)
  requires a.Length > 10
{
  // STIU:
  // forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]       (*)
  // a.Length > 10
  // VREAU SA DEMONSTREZ:
  // a[0] < a[1]
  // Ar fi util sa aleg in (*) i = 0 si j = 1
  // Din moment ce 0 <= i < j < a.Length, obtin a[i] < a[j], ceea ce voiam sa arat.
  assert a[0] < a[1];
}

method experiment4(a : array<int>)
  requires sorted2(a)
  requires a.Length > 10
{
  // STIU:
  // forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]       (*)
  // a.Length > 10
  // VREAU SA DEMONSTREZ:
  // a[0] < a[5]
  // Ar fi util sa aleg in (*) i = 0 si j = 5
  // Din moment ce 0 <= i = 0 < j = 5 < 10 < a.Length, obtin a[0] < a[5], ceea ce voiam sa arat.
  assert a[0] < a[5]; // FAILS
}


/*
   Mecanismul prin care sistemul ghiceste "i" sau "j" se numeste "triggering" (declansare).


   Sistemul "analizeaza" conditia:
   
   forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]

   Care ar fi valori bune pentru "i" si pentru "j"?

   De fiecare data cand este un acces la tabloul a:

       "... a[x] ...", incearca i = x si j = x.

   Exista un mecanism implict de declansare a cuantificatorului universal.

   Dar se poate controla si de catre utilizator.
 */

function identitate(x : int) : int
{
  x
}

predicate sorted3(a : array<int>)
  reads a
{
  forall i {:trigger identitate(i)}:: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1]
}

method experiment5(a : array<int>)
  requires sorted3(a)
  requires a.Length > 10
{
  // STIU:
  //   forall i {:trigger identitate(i)}:: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1] (*)
  // VREAU SA ARAT:
  //   a[0] < a[1]
  // deoarece nu este declansat niciodata trigger-ul, nu poate demonstra
  // FAILS: assert a[0] < a[1];
  assert identitate(0) == 0;
  // STIU:
  //   forall i {:trigger identitate(i)}:: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1] (*)
  //   identitate(0) == 0   // AH!!!
                            // am "declansat" i = 0 in (*)
  //   si deci obtin: 0 <= 0 < a.Length - 1 ==> a[0] < a[0 + 1]
  // VREAU SA ARAT:
  //   a[0] < a[1]
  
  assert a[0] < a[1];
}


method experiment6(a : array<int>)
  requires sorted3(a)
  requires a.Length > 10
{
  assert identitate(0) == 0;
  assert identitate(1) == 1;
  assert identitate(2) == 2;
  assert identitate(3) == 3;
  assert identitate(4) == 4;
  assert a[0] < a[5];
}

/*
   Prin acest mecanism, Dafny poate folosi formule cuantificate universal ca sa demonstreze
   lucruri interesante.

   LOGICA: mecanismul de triggerul este implementarea regulii de

   Gamma |- forall x.phi
   --------------------- ...
   Gamma |- phi[x / t]

   Mecanismul de declansare imi "propune" valori potential utile pentru "t".
 */

// Putem ajuta sistemul sa inteleaga ca sorted1 si sorted2 inseamna acelasi lucru.

lemma sorted2_sorted1(a : array<int>) // daca o metoda nu contine cod 
  requires sorted2(a)                  // pe care vreau sa il execut
  ensures sorted1(a)                   // pot sa ii spun metodei "lema"
{
}

lemma sorted1_aux_experiment(a : array<int>, i : int, j : int)
  requires sorted1(a)
  requires 0 <= i < j < a.Length
  requires a.Length > 10
  ensures a[0] < a[5]
{
  assert a[0] < a[1] < a[2] < a[3] < a[4] < a[5];
}

// Tehnica de demonstrare: prin inductie folosind o instructiune "while"
lemma sorted1_aux(a : array<int>, i : int, j : int)
  requires sorted1(a)
  requires 0 <= i < j < a.Length
  ensures a[i] < a[j]
{
  // assert a[i] < a[i + 1] < a[i + 2] < a[i + 3] < ... < a[j]
  var k := i + 1;
  while k < j                           // INDUCTIE
    invariant i + 1 <= k <= j             // STIU CA a[i] < a[k]
                                        //         k < j
    invariant a[i] < a[k]               // ARAT CA a[i] < a[k + 1]
  {
    //assert a[k - 1] < a[k];
    k := k + 1;
  }
}

lemma sorted1_sorted2(a : array<int>)
  requires sorted1(a)
  ensures sorted2(a)
{
  // STIU:
  //   a : array<int>
  //   forall i :: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1]
  // VREAU SA ARAT:
  //   forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]

  // INTUITIV:
  // Fie i, j a.i. 0 <= i < j < a.Length. ---> formalizeaza printr-o instructiune forall
  // Folosesc sorted1_aux(a, i, j) ca sa deduc ca a[i] < a[j].


  // instructiune "forall"
  forall i : int, j : int | 0 <= i < j < a.Length // fie i si j cu prop. 0<=i<j<a.Length
    ensures a[i] < a[j]                          // arat ca a[i] < a[j]
  {
    sorted1_aux(a, i, j); // apel la lema sorted1_aux:
    // requires sorted1(a)
    // requires 0 <= i < j < a.Length
    // ensures a[i] < a[j]

    // a[i] < a[j]
  }
  // cand "ies" dintr-o instructiune forall:
  // sistemul adauga in contextul curent
  //     forall i : int, j : int :: 0 <= i < j < a.Length ==> a[i] < a[j]
}


method binarySearch'(a : array<int>, x : int) returns (pos : int)
  requires sorted1(a)
  ensures pos == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
  ensures pos != -1 ==> 0 <= pos < a.Length && a[pos] == x
{
  sorted1_sorted2(a);
  var left := 0;
  var right := a.Length - 1;
  while left <= right
    invariant 0 <= left <= a.Length
    invariant -1 <= right < a.Length
    invariant forall i :: 0 <= i < left ==> a[i] < x           // 
    invariant forall i :: right < i < a.Length ==> a[i] > x   // 
  {
    var mid := (left + right) / 2;
    if x == a[mid] {
      return mid;
    } else if (x < a[mid]) {
      right := mid - 1;
    } else {
      left := mid + 1;
    }
  }
  return -1;
}

/*
   REGULA DE ELIMINARE A LUI FORALL:
   Daca sistemul stie o conditie de forma "forall x.P(x)",
   modul in care se foloseste de aceasta conditie este "triggering-ul".
   Alege valori convenabile pentru "x" in functie de continutul lui "P".
   
   REGULA DE INTRODUCERE A LUI FORALL:
   O folosesc cand vreau sa demonstrez o propozitie universala
   de forma "forall x.P(x)".
   Trebuie sa folosesc un forall-statement (o instructiune forall).
   Aleg arbitrar o valoare x.
   Arat ca P(x) are loc pentru valoarea arbitrar aleasa "x".
 */

/*

   Cum foloseste sistemul implicatii:
   
 */

method impl_experiment1(a : array<int>, i : int, j : int)
  requires 0 <= i < j < 10
  requires a.Length > 100
  requires 0 <= i < j < a.Length ==> a[i] < a[j]
  //ensures a[i] < a[j]
{
  assert a[i] < a[j]; // SISTEMUL SE POATE FOLOSI DE IMPLICATII IN MOD AUTOMAT
                      // DACA REUSESTE SA DEMONSTREZE ANTECEDENTUL
}

predicate interesant(x : int)
{
  x > 42
}

lemma x_modulo_2(x : int)
  requires x % 2 == 0
  ensures exists y :: x == 2 * y
{
  assume {:axiom} false; // deocamdata presupune fara sa demonstrezi
                         // ca lema are loc (si o revin la aceasta linie mai tarziu)
}

lemma impl_experiment2(x : int)
  requires x % 2 == 0
  requires (exists y :: x == 2 * y) ==> interesant(x) // sistemul foloseste
                                                // regula de eliminare a implicatiei
  ensures interesant(x)
{
  x_modulo_2(x);
}

// regula de introducere a implicatie
// Q: Cum demonstrez o implicatie?
// A: Folosesc un "if" in care presupun antecedentul si demonstrez doar consecventul.
method impl_experiment3(a : array<int>, i : int, j : int)
  requires sorted1(a)
  ensures 0 <= i < j < a.Length ==> a[i] < a[j]
{
  // ca sa demonstrez o implicatie, presupun antecedentul si demonstrez
  // consecventul.

  // cum presupun antecedentul? (si anume: 0 <= i < j < a.Length)
  if 0 <= i < j < a.Length {
    var k := i + 1;
    while k < j               
      invariant i + 1 <= k <= j 
      invariant a[i] < a[k]   
    {
      k := k + 1;
    }
  } else {
    // nu ma mai intereseaza
    // antecedentul fiind fals, implicatia in integralitatea ei este
    // in mod trivial adevarata.
  }
}

/*
   Rezumat IMPLICATII:
   Cum ma folosesc de o implicatie: demonstrez antecendetul si sistemul
   deduce automat consecventul.
   Cum demonstrez o implicatie: presupun antecedentul (folosind un if)
   si demonstrez consecventul.
   */



lemma x_modulo_2'(x : int)
  requires x % 2 == 0
  ensures exists y :: x == 2 * y
{
  // Cum demonstrez o propozitie existentiala?
  // Gasesc un martor pentru variabila cuantifica existential.
  var martor := x / 2;
  assert x == 2 * martor;
}

lemma x_modulo_2''(x : int)
  requires exists y :: x == 2 * y
  ensures x % 2 == 0
{
  // Cum folosesc o propozitie existentiala?
  var martor :| x == 2 * martor; // instructiunea assign-such-that
  assert x == 2 * martor;
}


lemma x_modulo_2'''(x : int)
  requires x % 2 == 0
  ensures exists y :: x == y * 2
{
  // Cum demonstrez o propozitie existentiala?
  // Gasesc un martor pentru variabila cuantifica existential.
  var martor := x / 2;
  assert x == 2 * martor; // cand vede "2 * _", nu se declanseaza nimic
  assert x == martor * 2; // cand vede "_ * 2", foloseste "_" ca declansator pentru "exists"
}

predicate declansator(y : int)
{
  true
}

lemma x_modulo_2''''(x : int)
  requires x % 2 == 0
  ensures exists y {:trigger declansator(y)} :: x == y * 2
{
  // Cum demonstrez o propozitie existentiala?
  // Gasesc un martor pentru variabila cuantifica existential.
  var martor := x / 2;
  assert declansator(martor);
}

/*
   REZUMAT EXISTS:
   - ca sa folosesc o propozitie existentiala: folosesc assign-such-that (var _ :| conditie)
   - ca sa demonstrez o propozitie existentiala: dau un martor care trebuie sa declanseze trigger-ul exists
 */

/*
   Pentru conectorii obisnuiti: SI, SAU, NOT, DUBLA IMPLICATIE ---> automat (similar cu implicatie)
 */

// Demonstratia prin reducere la absurd.
lemma exemplu_absurd(n : int)
  requires exists k :: n == 4 * k
  ensures exists k' :: n == 2 * k'
{
  if !exists k' :: n == 2 * k'
  {
    // stiu:
    // (1) exists k :: n == 4 * k
    // (2) !exists k' :: n == 2 * k'
    // vreau sa arat:
    // Fals
    var k :| n == 4 * k;
    assert forall k' :: n != 2 * k';
    assert n == 2 * (2 * k);
    assert false;
  } 
}

// PENTRU INDUCTIE sunt 2 variante de demonstrare:
// (1) folosind o instructiune repetitiva
// (2) folosind un apel recursiv
lemma sorted1_aux'(a : array<int>, i : int, j : int)
  requires sorted1(a)
  requires 0 <= i < j < a.Length
  ensures a[i] < a[j]
{
  if j == i + 1
  {
    assert a[i] < a[i + 1];
  }
  else
  {
    sorted1_aux'(a, i, j - 1); // imi aduce a[i] < a[j - 1]
    assert a[j - 1] < a[j];    // stiu asta din sorted1
  }
}


/*
   Rezumat:
   - cum putem ajuta sistemul sa demonstreze afirmatii pe care nu le poate
   demonstra automat (desi sunt adevarate)
   * &&, ||, ! (de cele mai multe ori, automat)
   * FORALL, EXISTS, ==>
   * reducere la absurd
   * inductie
 */

