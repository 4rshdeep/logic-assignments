// (In place) Selection sort (in non-descending order) on integer arrays by traversing the unsorted
// portion of the array from left to right and moving the maximum element to the right-most
// unsorted place.

method selectionSort(a:array<int>)
modifies a
{
    if a.Length > 1
    {
        var max, i : int;
        i := a.Length -1;
        max := 0;
        while i > 0
        invariant 0 <= i <= a.Length - 1
        invariant 0 <= max
        invariant max <= a.Length - 1
        {
            max := select(a, i);
            // swap
            a[i], a[max] := a[max], a[i];
            i := i - 1;
        }
    }
}

method select(a:array<int>, idx:int) returns (m : int)
requires 0 <= idx < a.Length
requires a.Length > 0
ensures 0 <= m < a.Length
{
    var j := idx;
    var max := 0;

    while j > 0
    invariant 0 <= j <= idx
    invariant 0 <= max <= idx
    decreases j
    {
        if a[j] > a[max] {
            max := j;
        }
        j := j-1;

    }
    m := max;

}

method Main ()
{
    var A := new int[10];

    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 4, 8, 8, 3, 5, 10, 9, 9, 4, 7;

    print "A = ", A[..], "\n";
    selectionSort(A);
    print "A = ", A[..], "\n";
}