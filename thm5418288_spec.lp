require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5418288 (m : El num) (n : El num) (h1 : Prf (<= m (SUC n))) : Prf (∀ (λ x : El num, (= ((@IN num) x (… m (SUC n))) ((@IN num) x ((@INSERT num) (SUC n) (… m n))))));
