require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5371007 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (= ((@INSERT num) n (… m (- n (NUMERAL (BIT1 _0))))) (… m n)))))));
