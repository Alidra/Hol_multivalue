require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7989574 [A N] : Prf (∀ (λ P : El (fun num (fun A bool)), (⇒ (∀ (λ i : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (<= i ((@dimindex N) (@UNIV N)))) ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_358 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_358 (P i x) x))))))))) ((@FINITE (cart A N)) ((@GSPEC (cart A N)) (λ GEN_PVAR_359 : El (cart A N), (∃ (λ v : El (cart A N), ((@SETSPEC (cart A N)) GEN_PVAR_359 (∀ (λ i : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (<= i ((@dimindex N) (@UNIV N)))) (P i ((@﹩ A N) v i))))) v)))))))));
