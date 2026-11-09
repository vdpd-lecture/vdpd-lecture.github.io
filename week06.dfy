class C<T(0)> {
//       ^^^
// caracteristica de tip (T are o valoare implicita)
  
  var mutableField: T
    
}

// class D<T> {
  
//   var mutableField: T
    
// }


class Cell
  //  invariant lungime >= 0 (in Dafny: nu se face asa)
  // invarianti de clasa (proprietate care e adevarata pe tot parcursul vietii unui obiect din clasa
  // respectiva)
{
  var lungime: int // nu vreau sa aiba sansa sa fie negativa
    // lungimea unui sir de caractere

    // cum pot informa sistemul ca lungime >= 0 in orice moment?

    // In Dafny, nu exista explicit notiunea de invariant de clasa.
    // In schimb se foloseste urmatoarea metodologie:
    // se declara un predicat "Valid" care intoarce true/false, dupa
    // cum obiectul respectiva invariantii pe care ii vreau.
  ghost predicate Valid()
    reads this
  {
    lungime >= 0
  }

  // la fiecare metoda/constructor, adaug un ensures cu Valid
  constructor(initValue : int) // constructor fara nume
    requires initValue >= 0
    ensures lungime == initValue
    ensures Valid()
  {
    lungime := initValue;
  }

  constructor fromNothing() // constructori cu nume
    ensures lungime == 0
    ensures Valid()
  {
    lungime := 0;
  }

  constructor fromString(s : string)
    ensures lungime == |s|
    ensures Valid()
  {
    lungime := |s|;
  }

  method increment()
    requires Valid()            // adaug preconditie cu invariantii de clasa
    modifies this
    ensures Valid()             // adaug postconditie cu invariantii de clasa
  {
    lungime := lungime + 1;
  }

  // // does not work
  // method decrement()
  //   requires Valid()            // adaug preconditie cu invariantii de clasa
  //   modifies this
  //   ensures Valid()             // adaug postconditie cu invariantii de clasa
  // {
  //   lungime := lungime - 1;
// }

  method decrementChoice1()
    requires lungime > 0
    requires Valid()            // adaug preconditie cu invariantii de clasa
    modifies this
    ensures Valid()             // adaug postconditie cu invariantii de clasa
    ensures lungime == old(lungime) - 1
  {
    lungime := lungime - 1;
  }

  method decrementChoice2()
    requires Valid()            // adaug preconditie cu invariantii de clasa
    modifies this
    ensures Valid()             // adaug postconditie cu invariantii de clasa
    ensures old(lungime) == 0 ==> lungime == 0
    ensures old(lungime) > 0 ==> lungime == old(lungime) - 1
  {
    if lungime == 0 {
      lungime := 0;
    } else {
      lungime := lungime - 1;
    }
  }

  method getLungime() returns (r : int)
    requires Valid()
    modifies this // am voie sa modific, nu neaparat ca garantez ca modific
    ensures Valid()
  {
    return lungime;
  }

  method setLungime(l : int)
    requires l >= 0
    modifies this
    ensures Valid()
  {
    lungime := l;
  }
}

method test1()
{
  var c : Cell := new Cell(10); // ensures c.Valid()
  var l := c.getLungime();  // modifies(c.getLungime()) == { c }
  assert c.Valid();        // 
}

method useCell()
{
  var c : Cell := new Cell(10);
  var d : Cell := new Cell.fromNothing();
  assert c.Valid();
  c.decrementChoice1();
  assert c.lungime == 9;
  c.decrementChoice2();
  assert c.lungime == 8;
}


class CC {
  
  var mutableField: int
    
  method Print() {
    print mutableField, "\n";
  }
  
  function Get(): int
    reads this
  {
    mutableField
  }
  
}


trait T
{
  method Print()
  {
    print("Hello, World!");
  }
}

class C2 extends T
{
  method RePrint()
  {
    Print();
  }
}

method useComplex()
{
  var c : Complex := new PolarComplex();
  var x := c.Real(); // c.Real() nu are voie sa citeasca
                    // nimic de pe heap
  // c.Real (care are voie sa citeasca "c" de pe heap)
}

trait Complex
{
  function Real() : real
    reads this
  function Im() : real
    reads this
}

class PolarComplex extends Complex
{
  var r : real
  var i : real
  constructor() { r := 0.0; i := 0.0; }  
    
  function Real(): real
    reads this
  {
    r
  }
  
  function Im(): real
    reads this
  {
    i
  }
}


class B
{
  var x: nat
    
  predicate Invariant()
    reads this
  {
    x % 2 == 0
  }
  
  constructor(x: nat)
    requires x % 2 == 0
    ensures Invariant()
  {
    this.x := x;
  }
  
  method Add(y: nat)
    requires Invariant()
    modifies this
    ensures Invariant()
  {
    this.x := this.x + 2 * y;
  }
  
  function Get(): nat
    requires Invariant()
    reads this
    ensures Get() % 2 == 0
  {
    x
  }
  
}

method Client()
{
  var b: B := new B(2);
  b.Add(3);
  var c: nat := b.Get(); // Error
}


class D
{
  var x : nat
    
  ghost const Repr: set<object> := { this }
  // paradigma: fiecare clasa sa aiba un camp ghost
  // (de obicei Repr, de la representation)
  // in care sa tinem minte toate obiectele
  // "accesibile" din clasa respectiva
}

class E
{
  method M(a: D)
    modifies a.Repr
  {
    a.x := 4;
  }
}


class Node
{
  const value: int

  ghost var secventa : seq<int>

  ghost var Repr: set<object> // ce credeti ca va contine Repr?
  // contine this, dar si toate nodurile accesibile (prin next)
  // pornind de la this

  ghost predicate Invariant()
    reads this, Repr
    decreases Repr
  {
    && |secventa| > 0
    && secventa[0] == value
    && this in Repr
    && (next != null ==>
      && next in Repr
      && next.secventa == secventa[1..]
      && next.Repr <= Repr
      && this !in next.Repr          // this nu este accesibil din
                                  // this.next
      && next.Invariant())
    && (next == null ==> |secventa| == 1)
  }

  var next: Node?

  constructor(value: int)
    ensures this.value == value
    ensures this.next == null
    ensures Invariant()
  {
    this.value := value;
    this.Repr := { this };
    this.secventa := [ value ];
    next := null;
  }

  method push_front(value: int) returns (r : Node)
    requires Invariant()
    ensures r.Invariant()
  {
    r := new Node(value);
    r.next := this;
    r.secventa := [ value ] + this.secventa;
    r.Repr := { r } + r.next.Repr;
  }

  function Head() : int
  {
    value
  }
  
  function Tail() : Node
    requires next != null
    reads this
  {
    next
  }

  function Len() : nat
    requires Invariant()
    reads this, Repr
    decreases Repr
  {
    if next == null then
      1
    else
      1 + next.Len()
  }

  method Append(l: Node)
    requires next == null
    requires Invariant()
    requires l.Invariant()
    requires Repr !! l.Repr // (Repr intersectat cu l.Repr == {})
    modifies Repr
    ensures Invariant()
  {
    next := l;
    Repr := Repr + l.Repr;
    secventa := [ value ] + l.secventa;
    assert this !in next.Repr;
  }

  // La laborator: Append unde nu stiu neaparat ca next == null
  // La curs: search recursiv
  // La laborator: search iterativ (folosind while)
  

  method search(info : int) returns (r : Node?)
    requires Invariant()
    decreases Repr
    ensures r != null ==> r.value == info
    // Nice try!
    // ensures r == null ==> forall node :: node in this.Repr ==>
    //                            node.value != info
    ensures r == null ==> forall i :: 0 <= i < |secventa| ==>
                           secventa[i] != info
  {
    if value == info {
      return this;
    } else if next == null {
      return null;
    } else {
      r := next.search(info);
    }
  }
}

method doesNotTerminate()
{
  var n1 := new Node(10);
  var n2 := new Node(20);
  n1.next := n2;
  n2.next := n1;
  //  var len := n1.Len();
}

method useLL()
{
  var l : Node := new Node(10);
}