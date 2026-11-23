# library name "A5"
GA5 := Group((1,2,3),(3,4,5));
# library name "3.L3(13)" (table is not in library)
GSL313 := SL(3, 13);
# library name "L3(13)" (table is not in library)
GPSL313 := PSL(3,13);
# library name "2^6:3.s6"
Gmax24 := Group([
          (1,18)(2,17)(3,7)(4,13)(5,8)(6,16)(9,21)(10,23)(11,19)(12,14)(15,20)(22,24),
          (1,18,22,14,12,19,4,13,21,2,17,3)(5,10,15,16)(6,7,23,24,20,9)(8,11) ]);
# unknown library name
Gmisc := SL(2, Integers mod 4);

