// checks whether array from indices low to high-1 are sorted
predicate sorted(a:array<int>, low:int, high:int) 
    requires 0 <= low <= high <= a.Length;
    reads a;
{
    forall j, k :: low <= j < k < high ==> a[j] <= a[k]
}

method selection_sort(a:array<int>)
    modifies a;
    requires a.Length > 0
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures sorted(a, 0, a.Length)
{
    var max : int;
    var i: int;
    i := a.Length-1;
    max := i;
    while i > 0
    invariant 0 <= i < a.Length;
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant sorted(a, i, a.Length); 
    invariant forall j :: 0 <= j < i < a.Length-1 ==> a[j] <= a[i+1] 
    decreases i;
    {
        max := select(a, i);
        a[i], a[max] := a[max], a[i];
        i := i-1;
    }
}

method select(a:array<int>, i: int) returns (m:int)
    requires 0 <= i < a.Length
    ensures 0 <= m <= i
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall x :: 0 <= x <= i ==> a[x] <= a[m]
{
    var j := i;
    m := j;
    while j > 0
    invariant 0 <= j <= i
    invariant 0 <= m <= i
    invariant forall x:: j <= x <= i ==> a[m] >= a[x]
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases j
    {
        j := j-1;
        if( a[j] > a[m])
        {
            m := j;
        }
    } 
}

method Main ()
{
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 4, 8, 8, 3, 5, 10, 9, 9, 4, 7;
    print "A = ", A[..], "\n";
    selection_sort(A);
    print "A = ", A[..], "\n";
}