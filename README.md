####  (C) 2025 Frank Lübeck (Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen)

# The GAP 4 package `CCTab'

This package provides programs to compute ordinary character tables of
finite groups, either interactively or automatically.

The automatic variant is based on Brauer's characterization of 
generalized characters and uses induction from p-elementary subgroups
C x P (C cyclic p'-group and P a p-group) and LLL-reduction.

This is explained in the article:

        W. R. Unger, Computing the character table of a finite group,
        Journal of Symbolic Computation 41 (2006), p. 847–862.

There is another GAP package 'InduceReduce' by Jonathan Gruber:

        https://github.com/gap-packages/InduceReduce

This package was created in an attempt to optimize the “InduceReduce” package.
Some ideas of this package were sketched in the following master thesis
which was supervised by the author of this package:

        Ulli Kehrle, Character tables by Unger's algorithm and 
        identification of conjugacy classes, Master Thesis, RWTH Aachen,
        2022.

## Installing and loading the package

Just download the archive from
   
       TODO

and unpack it in one of the 'pkg' directories of your GAP installation,
or clone the git repository

       git clone https://github.com/frankluebeck/CCTab.git

Then load the package with

       gap> LoadPackage("CCTab");


## Feedback

Use the issue tracker

       https://github.com/frankluebeck/CCTab/issues


## License

Distributed under the terms of the GNU General Public License (GPL) v3,
see the 'LICENSE' file for more details.

