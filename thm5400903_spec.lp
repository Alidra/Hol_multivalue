require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5400903 (m : El num) : Prf (= (∀ (λ x : El num, (= ((@IN num) x (… m (NUMERAL _0))) ((@IN num) x (@EMPTY num))))) (= (… m (NUMERAL _0)) (@EMPTY num)));
