function isGraph(n : int, s : array<int>, f : array<int>) : bool
	reads *
{
	s.Length == f.Length &&
		(forall i :: 0 <= i < s.Length ==> s[i] != f[i]) &&
		(forall i :: 0 <= i < s.Length ==> 0 <= s[i] < n) &&
		(forall i :: 0 <= i < s.Length ==> 0 <= f[i] < n)
}

function isSolution(coloring : seq<int>, n : int, s : array<int>, f : array<int>) : bool
	reads *
	requires isGraph(n, s, f)
{
	|coloring| == n &&
		(forall i :: 0 <= i < n ==> 0 <= coloring[i] <= 2) &&
		(forall j :: 0 <= j < s.Length ==> coloring[s[j]] != coloring[f[j]])
}

function isPartialSolution(coloring : seq<int>, n : int, s : array<int>, f : array<int>) : bool
	reads *
	requires isGraph(n, s, f)
{
	|coloring| <= n &&
		(forall i :: 0 <= i < |coloring| ==> 0 <= coloring[i] <= 2) &&
		(forall j :: 0 <= j < s.Length && s[j] < |coloring| && f[j] < |coloring| ==> coloring[s[j]] != coloring[f[j]])
}

method back(sol : seq<int>, n : int, s : array<int>, f : array<int>) returns (r : seq<int>)
	requires isGraph(n, s, f)
	requires n >= 1
	requires 0 <= |sol| <= n
	requires isPartialSolution(sol, n, s, f)
	ensures |r| == 0 ==> forall coloring : seq<int> :: sol <= coloring ==> !isSolution(coloring, n, s, f)
	ensures |r| > 0 ==> sol <= r && isSolution(r, n, s, f)
	decreases n - |sol|
{
	if (|sol| == n) {
		r := sol;
	} else {
		var i := 0;
		while (i <= 2)
			invariant forall j :: 0 <= j < i ==>
			  forall coloring : seq<int> :: sol + [j] <= coloring ==> !isSolution(coloring, n, s, f)
		{
			if (isPartialSolution(sol + [i], n, s, f)) {
				var r1 : seq<int> := back(sol + [i], n, s, f);
				if (|r1| != 0) {
					r := r1;
					return;
				}
			}
			i := i + 1;
		}
		assert forall coloring : seq<int> :: isSolution(coloring, n, s, f) && sol <= coloring ==>
			(sol + [0] <= coloring || sol + [1] <= coloring || sol + [2] <= coloring);
		r := [];
	}
}

method color(n : int, s : array<int>, f : array<int>) returns (r : seq<int>)
	requires isGraph(n, s, f)
	requires n >= 1
	ensures |r| == 0 ==> forall coloring : seq<int> :: !isSolution(coloring, n, s, f)
	ensures |r| > 0 ==> isSolution(r, n, s, f)
{
	r := back([], n, s, f);
}
