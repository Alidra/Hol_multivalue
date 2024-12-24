require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5400767 [A] (y : El A) (x : El A) (s : El (fun A bool)) : Prf ((λ s' : El (fun A bool), (= ((@IN A) x ((@INSERT A) y s')) (∨ (= x y) ((@IN A) x s')))) s);
