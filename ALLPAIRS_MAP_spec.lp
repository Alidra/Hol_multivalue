require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1184479 [_27538 _27539 _27540 _27541] (f : El (fun _27540 _27539)) (g : El (fun _27541 _27538)) : Prf (∀ (λ P : El (fun _27539 (fun _27538 bool)), (∀ (λ l : El (list _27540), (∀ (λ m : El (list _27541), (= ((@ALLPAIRS _27538 _27539) P ((@MAP _27540 _27539) f l) ((@MAP _27541 _27538) g m)) ((@ALLPAIRS _27541 _27540) (λ x : El _27540, (λ y : El _27541, (P (f x) (g y)))) l m))))))));
