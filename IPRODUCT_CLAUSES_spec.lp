require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6908823 [_126209 _126250] : Prf (∧ (∀ (λ f : El (fun _126209 int), (= ((@iproduct _126209) (@EMPTY _126209) f) (int_of_num (NUMERAL (BIT1 _0)))))) (∀ (λ x : El _126250, (∀ (λ f : El (fun _126250 int), (∀ (λ s : El (fun _126250 bool), (⇒ ((@FINITE _126250) s) (= ((@iproduct _126250) ((@INSERT _126250) x s) f) ((@COND int) ((@IN _126250) x s) ((@iproduct _126250) s f) (int_mul (f x) ((@iproduct _126250) s f))))))))))));
