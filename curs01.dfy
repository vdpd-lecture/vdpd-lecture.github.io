/*

   method test1()
{
  var r := max(8, 7);
  assert r == max_spec(8, 7);
}

// implementare
method max(x : int, y : int) returns (r : int)
  ensures r == max_spec(x, y)
{
  if x > y {
    return x;
  } else {
    return y;
  }
}

// specificatie funcțională a lui "max"
function max_spec(x : int, y : int) : int
{
  if x > y then x else y
}


// implementare
method max2(x : int, y : int) returns (r : int)
  ensures r >= x          // <- specificatie relationala
  ensures r >= y
{
  if x > y {
    return x + 7;
  } else {
    return y + 100;
  }
}

// implementare
method max3(x : int, y : int) returns (r : int)
  ensures r >= x          
  ensures r >= y
  ensures r == x || r == y
  // forall x, y :: r >= x && r >= y && (r == x || r == y)
{
  if x > y {
    return x;
  } else {
    return y;
  }
}

/*
// fails to verify:
method max_of_3(x : int, y : int, z : int) returns (r : int)
  ensures r >= x && r >= y && r >= z
  ensures r == x || r == y || r == z
{
  if (x > y && x > z) {
    return x;
  } else if (y > x && y > z) {
    return y;
  } else {
    return z; // x = 7, y = 7, z = 5
  }
}
 */
 */

method search(x : int, a : array<int>) returns (pos : int)
  ensures pos >= -1
  ensures pos < a.Length
  // ensures forall i :: 0 <= i < a.Length ==> a[pos] >= a[i] nu prea e o spec. pentru search
  //                                                     ci pentru un maxim
  ensures pos != -1 ==> a[pos] == x
  ensures pos == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
  var i := 0;
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != x
  {
    if (x == a[i]) {
      return i;
    }
    i := i + 1;
  }
  /*
     Stiu:
     0 <= i <= a.Length                (1)
     forall j :: 0 <= j < i ==> a[j] != x   (2)
     i >= a.Length                     (3)
     
     (1) + (3) i == a.Length           (4)
     (2) + (4) forall j :: 0 <= j < a.Length ==> a[j] != x
     --------------------------------/
     Trebuie sa arat:
     forall i :: 0 <= i < a.Length ==> a[i] != x
     */
  return -1;
}


method binarySearch(x : int, a : array<int>) returns (pos : int)
  // preconditie
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
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

method binarySearch'(x : int, a : array<int>) returns (pos : int)
  // preconditie
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // postconditie
  ensures pos >= -1
  ensures pos < a.Length
  ensures pos != -1 ==> a[pos] == x
  //ensures pos == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
  var left : int := 0;
  var right : int := a.Length;  
  while (left < right)
    invariant 0 <= left <= a.Length
    invariant -1 <= right <= a.Length
    // invariant forall i :: 0 <= i < left ==> a[i] < x               // Exercitiu: refaceti cei 2 invarianti comentati
    // invariant forall i :: right <= i < a.Length ==> a[i] > x
  {
    var middle := (left + right) / 2; // a = [ 7 ], x = 3, middle = 0
    if (a[middle] == x) {
      return middle;
    } else if (a[middle] < x) {
      left := middle + 1;
    } else {
      right := middle - 1; // middle = 0
    }
  }
  return -1;
}
