require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20230 [_3603] (P : El bool) (c : El _3603) (Q : El (fun _3603 bool)) : Prf (= T (⇒ (∀ (λ a : El _3603, (⇒ (= a c) (= P (Q a))))) (= P (∀ (λ a : El _3603, (⇒ (= a c) (Q a)))))));
