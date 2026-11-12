module

import RealRooted.ParkingFunctions.Descents.OrdinaryTransfer
import RealRooted.ParkingFunctions.Descents.TielessTransfer
import RealRooted.ParkingFunctions.Descents.WeakLeftPeakInterlacing

/-!
# Parking function challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "parking-functions"
formalized = "2026-09-13"
authors = ["Diaconis", "Hicks"]
tags = []
references = [
  "DiaconisHicks2017",
]

[[definitions]]
name = "ParkingFunction.IsParkingFunction"
module = "RealRooted.Mathlib.Combinatorics.Enumerative.ParkingFunction"
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
symcat = "parkingFunctionDescentsRealRooted"

[[theorems]]
name = """RealRooted.ParkingFunctions.\
parkingDescentPolynomialInt_succ_nsmul"""
module = "RealRooted.ParkingFunctions.Descents.OrdinaryTransfer"
label = "Pollak's cyclic action: descents of parking functions and of words"

[[theorems]]
name = "RealRooted.ParkingFunctions.map_tielessParkingDescentPolynomial_splits"
module = "RealRooted.ParkingFunctions.Descents.TielessTransfer"
label = "Tieless parking function descent polynomials are real-rooted"

[[theorems]]
name = "RealRooted.ParkingFunctions.succ_nsmul_tielessParkingDescentPolynomial_eq_chowPolynomial"
module = "RealRooted.ParkingFunctions.Descents.TielessTransfer"
label = "Tieless descents and a Brändén–Vecchi Chow polynomial"

[[theorems]]
name = "RealRooted.ParkingFunctions.map_parkingWeakLeftPeakPolynomialInt_splits"
module = "RealRooted.ParkingFunctions.Descents.WeakLeftPeakInterlacing"
label = "Parking function weak left peak polynomials are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Parking functions

The descent polynomial, the tieless descent polynomial and the weak left peak polynomial of
parking functions of length $n$ are real-rooted.

## Results

A [parking function](sf:parkingFunctionDefinition) of length $n$ [@DiaconisHicks2017] is a word
$w=w_0\dotsm w_{n-1}$ with letters in $\{0,\dots,n-1\}$ such that for every $k\le n$ at least
$k$ letters are smaller than $k$. We set
$\operatorname{des}(w)=\#\{i:w_i>w_{i+1}\}$ and
$\operatorname{wlpk}(w)=\#\{i\ge1:w_{i-1}\le w_i>w_{i+1}\}$, with positions numbered from $0$.
A parking function is *tieless* if no two adjacent letters are equal.

**Theorem.** For every $n\ge0$, each of the following polynomials over parking functions $w$ of
length $n$ is real-rooted:

- $\sum_w x^{\operatorname{des}(w)}$;
- $\sum_w x^{\operatorname{des}(w)}$ over tieless parking functions;
- $\sum_w x^{\operatorname{wlpk}(w)}$.

**Proposition.** For $n\ge0$, $(n+1)$ times the descent polynomial of the parking functions of
length $n$ equals the descent polynomial of all words of length $n$ over an alphabet of size
$n+1$ (Pollak's cyclic action). Also, $(n+1)$ times the tieless descent polynomial equals the
Brändén–Vecchi Chow polynomial of degree $n$ of the elementary Toeplitz matrix with $n+1$
entries equal to $1$.

## References

[@DiaconisHicks2017]. The Chow polynomials appear on the
[Brändén–Vecchi page](/RealRooted/theorems/branden-vecchi/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.ParkingFunctions.Descents`.
-/
