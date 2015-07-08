# Multiple Conclusion Intuitionistic Linear Logic and Cut Elimination

## Overview

This repository contains the [ Agda ](http://wiki.portal.chalmers.se/agda/) developments for the paper
[ Multiple Conclusion Intuitionistic Linear Logic and Cut Elimination ](http://metatheorem.org/papers/FILL-cut-report.pdf)
by Harley Eades III and Valeria de Paiva.

## Files

- [ prelude.agda ]( prelude.agda ) contains basic definitions used throughout the development.
- [ Dial2Sets.agda ]( Dial2sets.agda ) contains the definition of the basic dialectica category.
- [ FullLinCat.agda ]( FullLinCat.agda ) contains all of the constructions used in the proof that Dial2Sets is a full linear category.
- [ Tensorial.agda ]( Tensorial.agda ) contains all of the constructions used in the proof that Dial2Sets is a model of full tensor logic.

## Building

This development was tested with Agda version 2.4.2.3.  However, it
does not use the Agda standard library, but uses instead the Iowa Agda
Library version **ADD VERSION**.