require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3184698 [_83064] (P : El (fun (fun bool (fun _83064 bool)) bool)) (x : El _83064) : Prf (= ((@IN _83064) x ((@GSPEC _83064) (λ v : El _83064, (P ((@SETSPEC _83064) v))))) (P (λ p : El bool, (λ t : El _83064, (∧ p (= x t))))));
