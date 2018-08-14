// (In place) Selection sort (in non-descending order) on integer arrays by traversing the unsorted
// portion of the array from left to right and moving the maximum element to the right-most
// unsorted place.
predicate permutation (A:seq<int>, B:seq<int>) 
{
    multiset(A) == multiset(B)
}

predicate partOrdered(A:array<int>, lo:int, hi:int) 
    // requires A != null
    requires 0 <= lo <= hi <= A.Length
    reads A
{
    forall i, j :: lo <= i < j < hi ==> A[i] <= A[j]
}

predicate ordered(A:array<int>)
    // requires A != null
    reads A
{
    partOrdered(A, 0, A.Length)
}
method selectionSort(a:array<int>)
modifies a
// ensures ordered(a)
ensures permutation(a[..] , old(a[..]))
{
    if a.Length > 1
    {
        var max, i : int;
        i := a.Length -1;
        
        // var sorted_idx := a.Length - 1;
        max := i;
        while i > 0
        invariant 0 <= i < a.Length
        invariant permutation (a[..], old(a[..])) 
        invariant 0 <= max < a.Length
        // invariant partOrdered(a, i, a.Length)
        decreases i
        {   
            print i, " ";
            select(a, i); 
            // swap
            // a[i], a[max] := a[max], a[i];
            i := i - 1;
            print a[i..], "\n";
            print i, " ";
        }
    }
    print "\n";
}

// select max element from 0 to idx
method select(a:array<int>, idx:int )// returns (max : int)
modifies a
requires 0 <= idx < a.Length
// ensures 0 <= max <= idx
ensures forall x :: 0 <= x <= idx ==> a[x] <= a[idx]
ensures permutation (a[..], old(a[..]))
// ensures partOrdered(a, idx, a.Length)
{
    var j := idx;
    var max := idx;

    while j > 0
    invariant 0 <= j <= idx
    invariant 0 <= max <= idx
    invariant forall x :: j <= x <= idx ==> a[x] <= a[max]
    invariant permutation (a[..], old(a[..])) 
    decreases j
    {
        j := j-1;
        if a[j] > a[max] {
            max := j;
        }
    }
    a[idx], a[max] := a[max], a[idx];

}

method Main ()
{
    var A := new int[10];

    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 4, 8, 8, 3, 5, 10, 9, 9, 4, 7;

    print "A = ", A[..], "\n";
    selectionSort(A);
    print "A = ", A[..], "\n";
}