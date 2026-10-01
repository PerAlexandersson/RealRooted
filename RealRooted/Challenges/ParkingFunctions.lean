import RealRooted.ParkingFunctions.Descents.OrdinaryTransfer
import RealRooted.ParkingFunctions.Descents.TielessTransfer
import RealRooted.ParkingFunctions.Descents.WeakLeftPeakInterlacing

/-!
# Parking function challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "parking-functions"

[[definitions]]
name = "RealRooted.ParkingFunctions.IsParkingFunction"
module = "RealRooted.ParkingFunctions.Descents.Basic"
label = "Parking functions"

[[definitions]]
name = "RealRooted.ParkingFunctions.parkingDescentPolynomial"
module = "RealRooted.ParkingFunctions.Descents.Basic"
label = "Descent polynomial of parking functions"

[[definitions]]
name = "RealRooted.ParkingFunctions.tielessParkingDescentPolynomial"
module = "RealRooted.ParkingFunctions.Descents.Tieless"
label = "Descent polynomial of tieless parking functions"

[[definitions]]
name = "RealRooted.ParkingFunctions.parkingWeakLeftPeakPolynomialInt"
module = "RealRooted.ParkingFunctions.Descents.WeakLeftPeak"
label = "Weak left peak polynomial of parking functions"

[[theorems]]
name = "RealRooted.ParkingFunctions.parkingDescentPolynomial_splits"
module = "RealRooted.ParkingFunctions.Descents.OrdinaryTransfer"
label = "Parking function descent polynomials are real-rooted"
headline = true

[[theorems]]
name = """RealRooted.ParkingFunctions.\
succ_nsmul_parkingDescentPolynomialInt_eq_literalWordDescentPolynomialInt"""
module = "RealRooted.ParkingFunctions.Descents.OrdinaryTransfer"
label = "Pollak's cyclic action: descents of parking functions and of words"

[[theorems]]
name = "RealRooted.ParkingFunctions.map_tielessParkingDescentPolynomial_splits"
module = "RealRooted.ParkingFunctions.Descents.TielessTransfer"
label = "Tieless parking function descent polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.ParkingFunctions.succ_nsmul_tielessParkingDescentPolynomial_eq_chowPolynomial"
module = "RealRooted.ParkingFunctions.Descents.TielessTransfer"
label = "Tieless descents and a Brändén–Vecchi Chow polynomial"

[[theorems]]
name = "RealRooted.ParkingFunctions.map_parkingWeakLeftPeakPolynomialInt_splits"
module = "RealRooted.ParkingFunctions.Descents.WeakLeftPeakInterlacing"
label = "Parking function weak left peak polynomials are real-rooted"
headline = true
-->

<!-- realrooted-catalog-content -->
# Parking functions

A parking function of length `n` is a word `w` with letters in
`{0, …, n-1}` such that, for every `k ≤ n`, at least `k` of its letters are
smaller than `k`. The following
generating polynomials over parking functions of length `n` are formalized as
real-rooted:

- **Descents:** `sum_w x^des(w)`. The proof passes through Pollak's cyclic
  action: `(n+1)` times this polynomial equals the descent polynomial of all
  words of length `n` over an alphabet of size `n+1`.
- **Tieless descents:** the same count over parking functions with no two
  equal adjacent entries. `(n+1)` times this polynomial equals a
  Brändén–Vecchi Chow polynomial of an elementary Toeplitz matrix.
- **Weak left peaks:** `sum_w x^wlpk(w)`.

## References

P. Diaconis and A. Hicks, “Probabilizing parking functions,” *Adv. in Appl.
Math.* 89 (2017), 125–155.
The Chow polynomials appear on the
[Brändén–Vecchi page](/RealRooted/theorems/branden-vecchi/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.ParkingFunctions.Descents`.
-/
