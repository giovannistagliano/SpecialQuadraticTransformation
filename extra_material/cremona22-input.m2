---------------------            
-- Cremona of P^11 -- 
-- The following code computes the maps omega:P^11--->P^11, omega^{-1}:P^11--->P^11 and 
-- the parameterization gamma:P^6--->P^11.
---------------------

load "bir.m2";
kk=QQ;
ringP2=kk[t_0..t_2];
Lambda=intersect(ideal(t_0,t_1),ideal(t_0,t_2),ideal(t_1,t_2),ideal(t_0,t_1-t_2),
                 ideal(t_1,t_0-t_2),ideal(t_2,t_0-t_1),ideal(t_0-t_1,t_0-t_2));
ringP7=kk[u_0..u_7];
phi=map(ringP2,ringP7,gens image basis(4,Lambda));
Y=saturate kernel phi;
ringP11=kk[x_0..x_11];
psi=map(ringP7,ringP11,gens Y);
Z=ideal homogPartOfImage(psi,2);
omega=invertBirationalMapRS(matrix psi,Z);
omega=map(ringP11,ringP11,gens saturate ideal(gens Z|omega));
invomega=map(ringP11,ringP11,invertBirationalMapRS(matrix omega,ideal ringP11));
SecX=ideal sub((matrix(omega*invomega))_(0,0)/x_0,ringP11);
-- p is a smooth point of Sec(X)
p=ideal(x_10,x_9,x_8,x_7,x_6,x_5,x_4,x_3,x_2-x_11,x_1,x_0);
L=omega(preimage(omega,p)):(ideal matrix omega);
ringP6=kk[y_0..y_6];
pr=map(ringP11,ringP6,gens L);
gamma=map(ringP6,ringP11, sub(transpose 
            (invertBirationalMap(ideal matrix omega,gens L))#0,vars ringP6)); 
            
---------------------            
-- Cremona of P^20 --
-- The following code computes the maps omega:P^20--->P^20, omega^{-1}:P^20--->P^20 and 
-- the parameterization gamma:P^12--->P^20.
---------------------

load "bir.m2"; 
kk=QQ;
ringP8=kk[t_0..t_8];
E=ideal(-t_1*t_4+t_0*t_5,-t_2*t_4+t_0*t_6,-t_3*t_4+t_0*t_7,
        -t_2*t_5+t_1*t_6,-t_3*t_5+t_1*t_7,-t_3*t_6+t_2*t_7,        
        t_0^2+t_2^2+t_3^2+t_1*t_5+t_1*t_6+t_0*t_7,
        t_0*t_4+t_5^2+t_2*t_6+t_5*t_6+t_3*t_7+t_4*t_7);
ringP16=kk[u_0..u_16];
phi=map(ringP8,ringP16,matrix{{gens E,t_8*vars(ringP8)}});
Y=saturate kernel phi;
ringP20=kk[x_0..x_20];
psi=map(ringP16,ringP20,gens Y);
Z=ideal homogPartOfImage(psi,2);
omega=invertBirationalMapRS(matrix psi,Z);
omega=map(ringP20,ringP20,gens saturate ideal(gens Z|omega));
invomega=map(ringP20,ringP20,invertBirationalMapRS(matrix omega,ideal ringP20));
SecX=ideal sub((matrix(omega*invomega))_(0,0)/x_0,ringP20);
-- p is a smooth point of Sec(X)
p=ideal(x_19,x_18,x_17,x_16,x_15,x_14,x_13,x_12,x_11,x_10,
        x_9,x_8,x_7,x_6,x_5,x_4,x_3,x_2-x_20,x_1,x_0);
L=omega(preimage(omega,p)):(ideal matrix omega)
ringP12=kk[y_0..y_12];
pr=map(ringP20,ringP12,gens L);
gamma=map(ringP12,ringP20,sub(transpose 
            (invertBirationalMap(ideal matrix omega,gens L))#0,vars ringP12));
            
            

