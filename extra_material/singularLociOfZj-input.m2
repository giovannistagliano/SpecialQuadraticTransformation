load "equationsOfBj.m2";
for j to 2 list idealsingularLocusOfZ_j=trim ideal singularLocus Proj(ringTarget_j/Z_j);
F:=openOut "singularLociOfZj.m2";
F << "kk=QQ;"<<endl;
for j to 2 list F << "singularLocusOfZ_"<<j<<"=Proj(kk[y_0..y_(11-"<<j<<")]/"<<toString idealsingularLocusOfZ_j<<");"<<endl;
close F; 
exit
