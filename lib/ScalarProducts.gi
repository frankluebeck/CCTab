###########################################################################
##  ScalarProducts.gi
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to compute the scalar products of
##  generalized characters (Z-linear combinations of irreducible characters) 
##  of a finite group (also works for Q-linear combinations).
##  
##  Such class functions only need to be given on one conjugacy class of
##  every rational class, when power maps are available. The remaining
##  values for classes in the same rational class can be computed as 
##  Galois conjugates of the given values.
##  
##  This is used to store generalized characters in CCTable(G).
##  
##  The functions here can efficiently compute scalar products of
##  generalized characters given this way.
##  

# here we encode the data from RationalClassesInfo(G) needed to compute
# scalar products in a plain list of integers
InstallMethod(ScalarInfo, ["IsGroup"], function(G)
  local rci, res, pos, r;
  rci := RationalClassesInfo(G);
  # we change second entry to length + 1 later
  res := [Size(G), -1];
  pos := 3;
  for r in rci do
    if r.conductor = 1 then
      Append(res, [1, r.ind, pos+4, r.classlen]);
    else
      Append(res, [r.conductor, r.ind[1], pos+5+Length(r.ratvec),
                   r.dim, r.classlen]);
      Append(res, r.ratvec);
    fi;
    pos := Length(res)+1;
  od;
  res[2] := Length(res)+1;
  return res;
end);
InstallMethod(ScalarInfo, ["IsCCTable and HasUnderlyingGroup"], 
function(CCT)
  return ScalarInfo(UnderlyingGroup(CCT));
end);

##  <#GAPDoc Label="CCTScalarProduct">
##  <ManSection>
##  <Func Name="CCTScalarProduct" Arg="CCT, c, d"/>
##  <Returns>an integer</Returns>
##  <Description>
##  Let <A>CCT</A> be an <Ref Filt="IsCCTable"/> object, and let <A>c</A>
##  and <A>d</A> be two generalized characters of <A>CCT</A>, encoded as
##  integer vectors as produced by <Ref Func="EncodeForCCTable"/>.
##  This function returns the scalar product of <A>c</A> and <A>d</A>.
##  <P/>
##  This is used as the method for <Ref BookName="Reference"
##  Oper="ScalarProduct"/> for characters of an <Ref Filt="IsCCTable"/>
##  object. The <Package>CCTab</Package> also provides faster
##  implementations of this function as kernel extension. (It can be checked
##  if this is installed with 
##  <C>IsBound(CCTScalarProductInternal2);</C>.
##  <P/>
##  Note that this function cannot be used for arbitrary class functions,
##  it only works for class functions which are rational linear combinations of
##  irreducible characters.
##  <Example>
##  gap> G := AlternatingGroup(5);;
##  gap> CCT := CCTable(G);;
##  gap> irr := Irr(CCT);
##  [ [ 1, 1, 1, 1, 0, 0, 0 ], [ 3, -1, 0, 0, 0, -1, -1 ],
##    [ 3, -1, 0, 1, 0, 1, 1 ], [ 4, 0, 1, -1, 0, 0, 0 ],
##    [ 5, 1, -1, 0, 0, 0, 0 ] ]
##  gap> List(irr, c-> List(irr, d-> ScalarProduct(CCT, c, d)));
##  [ [ 1, 0, 0, 0, 0 ], [ 0, 1, 0, 0, 0 ], [ 0, 0, 1, 0, 0 ],
##    [ 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 1 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  Compute scalar product of generalized characters, only given the values
##  x on the classes i which start an entry of RatClassExps(G). The other
##  values on classes of the same rational class are GaloisCyc(x,kj), kj as
##  in RatClassExps.
##
BindGlobal("CCTScalarProduct",  function(CCT, c, d)
  local sci, done, res, pos, co, i, dim, rg, rv, x, j, y, n, k, m;
  sci := ScalarInfo(CCT);
  done := sci[2];
  res := 0;
  pos := 3;
  # loop over rational classes
  while pos < done do
    co := sci[pos];
    i := sci[pos+1];
    if co = 1 then
      if c[i] <> 0 and d[i] <> 0 then
        res := res + c[i] * d[i] * sci[pos+3];
      fi;
    else
      dim := sci[pos+3];
      rg := [0..dim-1];
      if ForAny(rg, j-> c[i+j] <> 0) and ForAny(rg, j-> d[i+j] <> 0) then
        x := 0;
        for k in [pos+5, pos+7..sci[pos+2]-2] do
          j := sci[k];
          y := 0;
          for m in [0..dim-1] do
            if c[i+m] <> 0 then
              n := m - j;
              if n < 0 then
                n := n+co;
              fi;
              if n < dim and d[i+n] <> 0 then
                y := y + c[i+m]*d[i+n];
              fi;
            fi;
          od;
          if y <> 0 then
            x := x + y * sci[k+1];
          fi;
        od;
        if x <> 0 then
          res := res + x * sci[pos+4];
        fi;
      fi;
    fi;
    pos := sci[pos+2];
  od;
  return res/sci[1];
end);

##  We have implementations of the previous function as kernel functions
##  CCTScalarProductInternal and CCTScalarProductInternal2.
##  If they are compiled we use them, otherwise the function above,
##  as method for ScalarProduct for characters of IsCCTable.
if IsBound(CCTScalarProductInternal) then
  InstallOtherMethod(ScalarProduct, ["IsCCTable", "IsList", "IsList"],
  function(CCT, c, d)
    return CCTScalarProductInternal2(ScalarInfo(CCT), c, d);
  end);
else
  InstallOtherMethod(ScalarProduct, ["IsCCTable", "IsList", "IsList"],
  function(CCT, c, d)
    return CCTScalarProduct(CCT, c, d);
  end);
fi;

