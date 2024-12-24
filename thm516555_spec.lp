require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem516555 : Prf (= T (∧ (∀ (λ n : El num, (= (ODD (NUMERAL n)) (ODD n)))) (∧ (= (ODD _0) F) (∧ (∀ (λ n : El num, (= (ODD (BIT0 n)) F))) (∀ (λ n : El num, (= (ODD (BIT1 n)) T)))))));
