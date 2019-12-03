function step_zero_Montgomery_min(X1, Z1, X2, Z2, X3, Z3, A)
  return (X2^2+Z2^2)^2, 4*X2*Z2*(X2^2+A*X2*Z2-Z2^2), 4*(X2*X3+Z2*Z3)^2*Z1, 4*(X2*Z3-Z2*X3)^2*X1;
end function;


function step_one_Montgomery_min(X1, Z1, X3, Z3, X2, Z2, A)
  return 4*(X2*X3+Z2*Z3)^2*Z1, 4*(X2*Z3-Z2*X3)^2*X1, (X2^2+Z2^2)^2, 4*X2*Z2*(X2^2+A*X2*Z2-Z2^2);  
end function;


function scalar_multiplication_Montgomery_min(n, X1, Z1, A)
  X2 := 1; Z2 := 0; X3 := X1; Z3 := Z1;
  nbits := Reverse(Intseq(n,2));
  if Z1 eq 0 then return "Error";
  else for i := 1 to #nbits do
    if nbits[i] eq 0 then X2, Z2, X3, Z3 := step_zero_Montgomery_min(X1, Z1, X2, Z2, X3, Z3, A);
    else X2, Z2, X3, Z3 := step_one_Montgomery_min(X1, Z1, X2, Z2, X3, Z3, A);
    end if;
  end for;
  return X2, Z2;
  end if;
end function;


function differential_addition_Montgomery_min(X1, Z1, X2, Z2, X3, Z3, A)
  if X1 eq 0 or Z1 eq 0 or [X2,Z2] eq [0,0] or [X3,Z3] eq [0,0] then return 0, 0;
  else
    return 4*(X2*X3+Z2*Z3)^2*Z1, 4*(X2*Z3-Z2*X3)^2*X1;
  end if;
end function;


function double_point_Montgomery_min(X2, Z2, A)
  if Z2 eq 0 or X2^3+A*X2^2+X2 eq 0 then return 0, 0;
  else return (X2^2+Z2^2)^2, 4*X2*Z2*(X2^2+A*X2*Z2-Z2^2);
  end if;
end function;


function act_with_ell_on_Montgomery_min(A, ell, xTors, xPush)
  XQ := xTors; ZQ := 1;
  pi := XQ; sigma := XQ + 1/XQ;
  fXPush := xPush*(XQ*xPush+1)^2; fZPush := (xPush-XQ)^2;
  if ell eq 3 then return pi^2*(A-6*sigma), fXPush, fZPush;
  else
  XQ, ZQ := double_point_Montgomery_min(XQ, ZQ, A); xQ := XQ/ZQ;
  pi *:= xQ; sigma +:= xQ + 1/xQ;
  fXPush *:= (xPush*xQ+1)^2; fZPush *:= (xPush - xQ)^2;
  XPrev := xTors; ZPrev := 1;
  for i in [3..(ell-1) div 2] do 
    XTemp := XQ; ZTemp := ZQ;
    XQ, ZQ := differential_addition_Montgomery_min(XPrev, ZPrev, xTors, 1, XQ, ZQ, A); xQ := XQ/ZQ;
    pi *:= xQ; sigma +:= xQ + 1/xQ;
    fXPush *:= (xPush*xQ+1)^2; fZPush *:= (xPush - xQ)^2;
    XPrev := XTemp; ZPrev := ZTemp;
  end for;
  end if;
  return pi^2*(A - 6*sigma), fXPush, fZPush;
end function;


function act_with_two_on_Montgomery_min(A, exp)
  A *:= Sign(exp);
  p := #Parent(A);
  sq_exp := (p+1) div 4;
  delta := (A^2 + 4)^sq_exp;
  if exp eq 0 then 
    return A;
  else
    A := 2*(A-3*delta)/(A+delta);
  end if;
  for i in [2..Abs(exp)] do
    eps := (A^2 - 4)^sq_exp;
    A := 2*(3 - A*(A - eps));
  end for;
  eps := (A^2 - 4)^sq_exp;
  scalefac := (eps*(eps + A)/2)^sq_exp;
  return Sign(exp)*(-A-3*eps)/(2*scalefac);
end function;


function csurf_action(private_key, A)
  ells := [ 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 
103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 
223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 
349, 353, 367, 373, 379, 383, 389 ];
  p := 2^3*3*&*ells - 1;
  F := GF(p);
  A := F ! A;
  A := act_with_two_on_Montgomery_min(A,private_key[1]);
  private_key := Remove(private_key, 1);
  while private_key ne [0 : i in [1..74]] do
    xP := Random(F);
    twist := not IsSquare(xP^3+A*xP^2-xP); if twist then A := -A; xP := -xP; end if;
    indices_ells_correct_sign := [];
    k := 1;
    for i := 1 to #ells do
      if private_key[i] gt 0 and not twist then Append(~indices_ells_correct_sign,i); k *:= ells[i];
      elif private_key[i] lt 0 and twist then Append(~indices_ells_correct_sign,i); k *:= ells[i];
      end if;
    end for;
    XQ, ZQ := scalar_multiplication_Montgomery_min((p+1) div k, xP, 1, A);
    for i in indices_ells_correct_sign do
      if ells[i] eq 3 then
        if ZQ ne 0 then
          xQ := XQ/ZQ;
          XR9, ZR9 := scalar_multiplication_Montgomery_min(k div 3, xQ, 1, A);
          if ZR9 ne 0 then
            XR, ZR := scalar_multiplication_Montgomery_min(3, XR9/ZR9, 1, A);
            if ZR eq 0 then
              A, XQ, ZQ := act_with_ell_on_Montgomery_min(A, 3, XR9/ZR9, xQ);
              if twist then private_key[i] +:= 1; else private_key[i] -:= 1; end if;
            else
              A, XQ, ZQ := act_with_ell_on_Montgomery_min(A, 3, XR/ZR, xQ);
              if twist then private_key[i] +:= 1; else private_key[i] -:= 1; end if;
            end if;
          end if;
        end if;
      else
        if ZQ ne 0 then
          xQ := XQ/ZQ;
          ell := ells[i];
          XR, ZR := scalar_multiplication_Montgomery_min(k div ell, xQ, 1, A);
          if ZR ne 0 then
            A, XQ, ZQ := act_with_ell_on_Montgomery_min(A, ell, XR/ZR, xQ);
            if twist then private_key[i] +:= 1; else private_key[i] -:= 1; end if;
          end if;
        end if;
      end if;
    end for;
    if twist then A := -A; end if;
  end while;
  return A;
end function;


function csurf_private_keygen()
  return [Random([-137..137])] cat [Random([-4..4]) : i in [1..3]] 
         cat [Random([-5..5]) : i in [1..46]] cat [Random([-4..4]) : i in [1..25]];
end function;


procedure csurf_key_exchange()
  t := Cputime();
  alice_private := csurf_private_keygen();
  bob_private := csurf_private_keygen();
  alice_public := csurf_action(alice_private,0);
  printf "Alice's public key is %o.\n", alice_public;
  bob_public := csurf_action(bob_private,0);
  printf "Bob's public key is %o.\n", bob_public;
  alice_bob := csurf_action(alice_private, bob_public);
  bob_alice := csurf_action(bob_private, alice_public);
  if alice_bob ne bob_alice then
    print "Error! The computations of the joint key do not match.";
  else
    printf "The computation took %o seconds.\n", Cputime(t);
    printf "The joint key is %o.\n", alice_bob;
  end if;
end procedure;