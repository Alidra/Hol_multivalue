require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5400913 (m : El num) (n : El num) : Prf (= (∀ (λ x : El num, (= ((@IN num) x (… m (SUC n))) ((@IN num) x (… m n))))) (= (… m (SUC n)) (… m n)));
