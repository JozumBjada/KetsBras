# KetsBras
Unfinished package of functions for quantum object manipulation in Wolfram language

The package uses predefined symbols `Ket` and `Bra` to represent kets and bras, operators are represented as linear combination of the form `Ket[k]**Bra[b]`. The tensor product is implemented using `NonCommutativeMultiply` (`**`) such that e.g. `Ket[a,b]` is the same as `Ket[a]**Ket[b]`.

There are two types of bases - finite, given by an explicit list of kets, and infinite, defined by a label.

TODO

## API Overview

### Bases

- **onBases** - list of available orthonormal bases
- **addBasis** - add a basis to the list of bases
- **clearBasis** - remove a bases from the list

- **$onBasesTransformations** - list of 
- **addBasisTransformation** - 
- **clearBasisTransformation** - 

- **basisQ** -
- **basisVectorQ** - 
- **changeBasis** - 
- **checkBasisTr** - 


- **identifyBases** - 
- **infiniteBasis** - 
- **infiniteBasisQ** - 

- **getInfiniteLabel** - 
- **$evaluateBasisProduct** - 

### Kets

- **permuteKets** - 
- **replaceKet** - 
- **unfactorKetsList** - 
- **factorKetsList** - 
- **fromKet** - 
- **toKet** - 
- **generateKets** - 
- **idket** - 
- **k0, k1, kd, ka, kr, kl, psip, psim, phip, phim** - 
- **kroneckerKetProducts** - 
- **linearCombinationQ** - 

### Operators

- **fromKetBra** - 
- **toKetBra** - 
- **partTr** - 

