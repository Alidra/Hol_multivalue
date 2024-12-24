require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3791010 [A B] (f : El (fun A (fun B B))) (s : El (fun A bool)) (a : El B) (b : El B) : Prf (= ((λ b' : El B, (= ((@FINREC A B) f b' s a (NUMERAL _0)) (∧ (= s (@EMPTY A)) (= a b')))) b) (= ((@FINREC A B) f b s a (NUMERAL _0)) (∧ (= s (@EMPTY A)) (= a b))));
