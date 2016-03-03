# Multiple Conclusion Linear Logic: Cut Elimination and more

## Overview

This repository contains the [ Agda ](http://wiki.portal.chalmers.se/agda/) developments for the paper
[ Multiple Conclusion Linear Logic: Cut Elimination and more ](http://metatheorem.org/papers/FILL-report.pdf)
by Harley Eades III and Valeria de Paiva.

## Files

- [ prelude.agda ]( prelude.agda ) contains basic definitions used throughout the development.  
- [lineale.agda]( lineale.agda ) contains the definition of lineales.
- [lineale-thms.agda]( lineale-thms.agda ) contains results about lineales.
- [ DialSets.agda ]( DialSets.agda ) contains the definition of the basic dialectica category.
- [ FullLinCat.agda ]( FullLinCat.agda ) contains all of the constructions used in the proof that Dial2Sets is a full linear category.
- [ Tensorial.agda ]( Tensorial.agda ) contains all of the constructions used in the proof that Dial2Sets is a model of full tensor logic.

## Building

This development was tested with Agda 2.4.2.4 and depends on the
[Augusta University Agda Library](https://github.com/heades/AUGL).