Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_PSUBSET_EMPTY_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem3228061 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3228062 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3228061 A s t). Qed.
Lemma lem3228063 {A : Type'} (s : A -> Prop) : (@PSUBSET A s (@EMPTY A)) = (term1 A s).
Proof. exact (@lem3228062 A s (@EMPTY A)). Qed.
Lemma lem3228067 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3228068 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term2 A s t).
Proof. exact (@lem3228067 A s t). Qed.
Lemma lem3228069 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@EMPTY A)) = (term3 A s).
Proof. exact (@lem3228068 A s (@EMPTY A)). Qed.
Lemma lem3228076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228077 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A s).
Proof. exact (MK_COMB (@lem3228076) (@lem3228069 A s)). Qed.
Lemma lem3228081 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3228082 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (@lem3228081 A s t). Qed.
Lemma lem3228083 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term7 A s).
Proof. exact (@lem3228082 A s (@EMPTY A)). Qed.
Lemma lem3228092 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228093 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (MK_COMB (@lem3228092) (@lem3228083 A s)). Qed.
Lemma lem3228094 {A : Type'} (s : A -> Prop) : (term1 A s) = (term10 A s).
Proof. exact (MK_COMB (@lem3228077 A s) (@lem3228093 A s)). Qed.
Lemma lem3228097 {A : Type'} (s : A -> Prop) : (@PSUBSET A s (@EMPTY A)) = (term10 A s).
Proof. exact (TRANS (@lem3228063 A s) (@lem3228094 A s)). Qed.
Lemma lem3228098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228099 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem3228098) (@lem3228097 A s)). Qed.
Lemma lem3228100 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228099 A s)). Qed.
Lemma lem3228101 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228102 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem3228101 A) (@lem3228100 A)). Qed.
Lemma lem3228107 {A : Type'} : (term16 A) = (term15 A).
Proof. exact (SYM (@lem3228102 A)). Qed.
Lemma lem3228121 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3228122 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3228121 A P x). Qed.
Lemma lem3228123 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3228122 A s x). Qed.
Lemma lem3228124 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3228125 {A : Type'} (s : A -> Prop) (x : A) : (term17 A x s) = (term18 A s x).
Proof. exact (MK_COMB (@lem3228124) (@lem3228123 A s x)). Qed.
Lemma lem3228127 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3228128 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3228127 A x). Qed.
Lemma lem3228129 {A : Type'} (s : A -> Prop) (x : A) : (term19 A s x) = (term20 A s x).
Proof. exact (MK_COMB (@lem3228125 A s x) (@lem3228128 A x)). Qed.
Lemma lem3228131 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem3228132 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = (term21 A s x).
Proof. exact (@lem3228131 (s x)). Qed.
Lemma lem3228133 {A : Type'} (s : A -> Prop) (x : A) : (term19 A s x) = (term21 A s x).
Proof. exact (TRANS (@lem3228129 A s x) (@lem3228132 A s x)). Qed.
Lemma lem3228134 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (fun_ext (fun x : A => @lem3228133 A s x)). Qed.
Lemma lem3228135 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228136 {A : Type'} (s : A -> Prop) : (term3 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem3228135 A) (@lem3228134 A s)). Qed.
Lemma lem3228141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228142 {A : Type'} (s : A -> Prop) : (term5 A s) = (term25 A s).
Proof. exact (MK_COMB (@lem3228141) (@lem3228136 A s)). Qed.
Lemma lem3228150 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3228151 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3228150 A P x). Qed.
Lemma lem3228152 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3228151 A s x). Qed.
Lemma lem3228153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3228154 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3228153) (@lem3228152 A s x)). Qed.
Lemma lem3228156 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3228157 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3228156 A x). Qed.
Lemma lem3228158 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3228154 A s x) (@lem3228157 A x)). Qed.
Lemma lem3228160 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3228161 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term21 A s x).
Proof. exact (@lem3228160 (s x)). Qed.
Lemma lem3228162 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term21 A s x).
Proof. exact (TRANS (@lem3228158 A s x) (@lem3228161 A s x)). Qed.
Lemma lem3228163 {A : Type'} (s : A -> Prop) : (term28 A s) = (term23 A s).
Proof. exact (fun_ext (fun x : A => @lem3228162 A s x)). Qed.
Lemma lem3228164 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228165 {A : Type'} (s : A -> Prop) : (term7 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem3228164 A) (@lem3228163 A s)). Qed.
Lemma lem3228170 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228171 {A : Type'} (s : A -> Prop) : (term9 A s) = (term29 A s).
Proof. exact (MK_COMB (@lem3228170) (@lem3228165 A s)). Qed.
Lemma lem3228172 {A : Type'} (s : A -> Prop) : (term10 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3228142 A s) (@lem3228171 A s)). Qed.
Lemma lem3228175 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228176 {A : Type'} (s : A -> Prop) : (term12 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3228175) (@lem3228172 A s)). Qed.
Lemma lem3228177 {A : Type'} : (term14 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228176 A s)). Qed.
Lemma lem3228178 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228179 {A : Type'} : (term16 A) = (term33 A).
Proof. exact (MK_COMB (@lem3228178 A) (@lem3228177 A)). Qed.
Lemma lem3228184 {A : Type'} : (term33 A) = (term16 A).
Proof. exact (SYM (@lem3228179 A)). Qed.
Lemma lem3228186 (p : Prop) : p = (term34 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3228187 {A : Type'} : (term33 A) = (term35 A).
Proof. exact (@lem3228186 (term33 A)). Qed.
Lemma lem3228188 {A : Type'} : (term35 A) = (term33 A).
Proof. exact (SYM (@lem3228187 A)). Qed.
Lemma lem3228189 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3228192 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem3228193 {A : Type'} : term37 A.
Proof. exact (fun h0 : term35 A => @lem3228192 A h0). Qed.
Lemma lem3228194 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (h1). Qed.
Lemma lem3228195 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem3228196 {A : Type'} (h1 : term35 A) (h2 : term37 A) : term35 A.
Proof. exact (@lem3228194 A h2 (@lem3228195 A h1)). Qed.
Lemma lem3228197 {A : Type'} (h1 : term35 A) : term38 A.
Proof. exact (fun h0 : term37 A => @lem3228196 A h1 h0). Qed.
Lemma lem3228198 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (h1). Qed.
Lemma lem3228199 {A : Type'} (h1 : term35 A) (h2 : term37 A) : term35 A.
Proof. exact (@lem3228197 A h1 (@lem3228198 A h2)). Qed.
Lemma lem3228200 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (fun h0 : term35 A => @lem3228199 A h0 h1). Qed.
Lemma lem3228201 {A : Type'} : term39 A.
Proof. exact (fun h0 : term37 A => @lem3228200 A h0). Qed.
Lemma lem3228204 {A : Type'} : term37 A.
Proof. exact (@lem3228201 A (@lem3228193 A)). Qed.
Lemma lem3228205 {A : Type'} : term37 A.
Proof. exact (@lem3228204 A). Qed.
Lemma lem3228207 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3228208 {A : Type'} : (term35 A) = (term40 A).
Proof. exact (@lem3228207 (term36 A)). Qed.
Lemma lem3228210 (t : Prop) : (term41 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3228211 {A : Type'} : (term40 A) = (term33 A).
Proof. exact (@lem3228210 (term33 A)). Qed.
Lemma lem3228230 {A : Type'} : (term35 A) = (term33 A).
Proof. exact (TRANS (@lem3228208 A) (@lem3228211 A)). Qed.
Lemma lem3228233 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = (term21 A s x).
Proof. exact (eq_refl (term21 A s x)). Qed.
Lemma lem3228234 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (fun_ext (fun x : A => @lem3228233 A s x)). Qed.
Lemma lem3228235 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228236 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem3228235 A) (@lem3228234 A s)). Qed.
Lemma lem3228237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228238 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (MK_COMB (@lem3228237) (@lem3228236 A s)). Qed.
Lemma lem3228241 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = (term21 A s x).
Proof. exact (eq_refl (term21 A s x)). Qed.
Lemma lem3228242 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (fun_ext (fun x : A => @lem3228241 A s x)). Qed.
Lemma lem3228243 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228244 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem3228243 A) (@lem3228242 A s)). Qed.
Lemma lem3228245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228246 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (MK_COMB (@lem3228245) (@lem3228244 A s)). Qed.
Lemma lem3228247 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3228246 A s) (@lem3228238 A s)). Qed.
Lemma lem3228248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228249 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3228248) (@lem3228247 A s)). Qed.
Lemma lem3228250 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228249 A s)). Qed.
Lemma lem3228251 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228252 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem3228251 A) (@lem3228250 A)). Qed.
Lemma lem3228275 {A : Type'} : (term35 A) = (term33 A).
Proof. exact (TRANS (@lem3228230 A) (@lem3228252 A)). Qed.
Lemma lem3228276 {A : Type'} : (term33 A) = (term35 A).
Proof. exact (SYM (@lem3228275 A)). Qed.
Lemma lem3228277 {A : Type'} (s : A -> Prop) (h1 : term30 A s) : term30 A s.
Proof. exact (h1). Qed.
Lemma lem3228278 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = (term21 A s x).
Proof. exact (eq_refl (term21 A s x)). Qed.
Lemma lem3228279 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (fun_ext (fun x : A => @lem3228278 A s x)). Qed.
Lemma lem3228280 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228281 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem3228280 A) (@lem3228279 A s)). Qed.
Lemma lem3228284 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3228285 {A : Type'} (P : A -> Prop) : (term43 A P) = (term44 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3228286 {A : Type'} (s : A -> Prop) : (term29 A s) = (term45 A s).
Proof. exact (@lem3228285 A (term23 A s)). Qed.
Lemma lem3228287 {A : Type'} (s : A -> Prop) (x : A) : (term46 A s x) = (term21 A s x).
Proof. exact (eq_refl (term46 A s x)). Qed.
Lemma lem3228288 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228289 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term42 A s x).
Proof. exact (MK_COMB (@lem3228288) (@lem3228287 A s x)). Qed.
Lemma lem3228290 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (s x).
Proof. exact (TRANS (@lem3228289 A s x) (@lem3228284 A s x)). Qed.
Lemma lem3228291 {A : Type'} (s : A -> Prop) : (term48 A s) = (term49 A s).
Proof. exact (fun_ext (fun x : A => @lem3228290 A s x)). Qed.
Lemma lem3228292 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3228293 {A : Type'} (s : A -> Prop) : (term45 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem3228292 A) (@lem3228291 A s)). Qed.
Lemma lem3228294 {A : Type'} (s : A -> Prop) : (term29 A s) = (term50 A s).
Proof. exact (TRANS (@lem3228286 A s) (@lem3228293 A s)). Qed.
Lemma lem3228295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228296 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (MK_COMB (@lem3228295) (@lem3228281 A s)). Qed.
Lemma lem3228297 {A : Type'} (s : A -> Prop) : (term30 A s) = (term51 A s).
Proof. exact (MK_COMB (@lem3228296 A s) (@lem3228294 A s)). Qed.
Lemma lem3228308 {A : Type'} (P : Prop) (Q : A -> Prop) : (term52 A P Q) = (term53 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3228309 {A : Type'} (P : Prop) (Q : A -> Prop) : (term52 A P Q) = (term53 A P Q).
Proof. exact (@lem3228308 A P Q). Qed.
Lemma lem3228311 {A : Type'} (s : A -> Prop) : (term51 A s) = (term54 A s).
Proof. exact (@lem3228309 A (term24 A s) s). Qed.
Lemma lem3228312 {A : Type'} (s : A -> Prop) : (term30 A s) = (term54 A s).
Proof. exact (TRANS (@lem3228297 A s) (@lem3228311 A s)). Qed.
Lemma lem3228313 {A : Type'} (s : A -> Prop) (h1 : term30 A s) : term54 A s.
Proof. exact (EQ_MP (@lem3228312 A s) (@lem3228277 A s h1)). Qed.
Lemma lem3228314 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term55 A s x.
Proof. exact (h1). Qed.
Lemma lem3228317 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3228322 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = (term21 A s x).
Proof. exact (eq_refl (term21 A s x)). Qed.
Lemma lem3228323 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (fun_ext (fun x : A => @lem3228322 A s x)). Qed.
Lemma lem3228324 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228325 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem3228324 A) (@lem3228323 A s)). Qed.
Lemma lem3228326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228327 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (MK_COMB (@lem3228326) (@lem3228325 A s)). Qed.
Lemma lem3228328 {A : Type'} (s : A -> Prop) (x : A) : (term55 A s x) = (term55 A s x).
Proof. exact (MK_COMB (@lem3228327 A s) (@lem3228317 A s x)). Qed.
Lemma lem3228329 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term55 A s x.
Proof. exact (EQ_MP (@lem3228328 A s x) (@lem3228314 A s x h1)). Qed.
Lemma lem3228331 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term24 A s.
Proof. exact (proj1 (@lem3228329 A s x h1)). Qed.
Lemma lem3228333 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = (term21 A s x).
Proof. exact (eq_refl (term21 A s x)). Qed.
Lemma lem3228334 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (fun_ext (fun x : A => @lem3228333 A s x)). Qed.
Lemma lem3228335 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228337 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem3228335 A) (@lem3228334 A s)). Qed.
Lemma lem3228338 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term24 A s.
Proof. exact (EQ_MP (@lem3228337 A s) (@lem3228331 A s x h1)). Qed.
Lemma lem3228343 {A : Type'} (_33175 : A) (s : A -> Prop) (x : A) (h1 : term55 A s x) : term46 A s _33175.
Proof. exact (@lem3228338 A s x h1 _33175). Qed.
Lemma lem3228344 {A : Type'} (s : A -> Prop) (_33175 : A) : (term46 A s _33175) = (term21 A s _33175).
Proof. exact (eq_refl (term46 A s _33175)). Qed.
Lemma lem3228347 {A : Type'} (_33175 : A) (s : A -> Prop) (x : A) (h1 : term55 A s x) : term21 A s _33175.
Proof. exact (EQ_MP (@lem3228344 A s _33175) (@lem3228343 A _33175 s x h1)). Qed.
Lemma lem3228351 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : s x.
Proof. exact (proj2 (@lem3228329 A s x h1)). Qed.
Lemma lem3228352 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term56 A s x.
Proof. exact (fun h0 : term21 A s x => @lem3228351 A s x h1). Qed.
Lemma lem3228354 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3228355 {A : Type'} (s : A -> Prop) (x : A) : (term56 A s x) = (s x).
Proof. exact (@lem3228354 (s x)). Qed.
Lemma lem3228356 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : s x.
Proof. exact (EQ_MP (@lem3228355 A s x) (@lem3228352 A s x h1)). Qed.
Lemma lem3228359 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3228361 {A : Type'} (s : A -> Prop) (_33175 : A) : (term21 A s _33175) = (term20 A s _33175).
Proof. exact (@lem3228359 (s _33175)). Qed.
Lemma lem3228364 {A : Type'} (_33175 : A) (s : A -> Prop) (x : A) (h1 : term55 A s x) : term20 A s _33175.
Proof. exact (EQ_MP (@lem3228361 A s _33175) (@lem3228347 A _33175 s x h1)). Qed.
Lemma lem3228365 {A : Type'} (_33175 : A) (s : A -> Prop) (x : A) (h1 : term55 A s x) : term20 A s _33175.
Proof. exact (@lem3228364 A _33175 s x h1). Qed.
Lemma lem3228366 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term20 A s x.
Proof. exact (@lem3228365 A x s x h1). Qed.
Lemma lem3228369 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : False.
Proof. exact (@lem3228366 A s x h1 (@lem3228356 A s x h1)). Qed.
Lemma lem3228370 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term58.
Proof. exact (fun h0 : ~ False => @lem3228369 A s x h1). Qed.
Lemma lem3228372 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3228373 : term58 = False.
Proof. exact (@lem3228372 False). Qed.
Lemma lem3228374 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : False.
Proof. exact (EQ_MP (@lem3228373) (@lem3228370 A s x h1)). Qed.
Lemma lem3228375 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : (term55 A s x) = False.
Proof. exact (prop_ext (fun h2 : term55 A s x => @lem3228374 A s x h1) (fun h2 : False => @lem3228329 A s x h1)). Qed.
Lemma lem3228376 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : False.
Proof. exact (EQ_MP (@lem3228375 A s x h1) (@lem3228329 A s x h1)). Qed.
Lemma lem3228377 {A : Type'} (s : A -> Prop) (h1 : term30 A s) : False.
Proof. exact (ex_elim (@lem3228313 A s h1) (fun x : A => fun h0 : term59 A s x => @lem3228376 A s x h0)). Qed.
Lemma lem3228378 {A : Type'} (s : A -> Prop) : term60 A s.
Proof. exact (fun h0 : term30 A s => @lem3228377 A s h0). Qed.
Lemma lem3228379 {A : Type'} (s : A -> Prop) : (term60 A s) = (term31 A s).
Proof. exact (@lem69 (term30 A s)). Qed.
Lemma lem3228380 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (EQ_MP (@lem3228379 A s) (@lem3228378 A s)). Qed.
Lemma lem3228385 {A : Type'} : term33 A.
Proof. exact (fun s : A -> Prop => @lem3228380 A s). Qed.
Lemma lem3228386 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem3228276 A) (@lem3228385 A)). Qed.
Lemma lem3228388 {A : Type'} : term35 A.
Proof. exact (@lem3228205 A (@lem3228386 A)). Qed.
Lemma lem3228389 {A : Type'} (h1 : term36 A) : False.
Proof. exact (@lem3228388 A (@lem3228189 A h1)). Qed.
Lemma lem3228390 {A : Type'} (h1 : term36 A) : (term36 A) = False.
Proof. exact (prop_ext (fun h2 : term36 A => @lem3228389 A h1) (fun h2 : False => @lem3228189 A h1)). Qed.
Lemma lem3228391 {A : Type'} (h1 : term36 A) : False.
Proof. exact (EQ_MP (@lem3228390 A h1) (@lem3228189 A h1)). Qed.
Lemma lem3228392 {A : Type'} : term35 A.
Proof. exact (fun h0 : term36 A => @lem3228391 A h0). Qed.
Lemma lem3228393 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem3228188 A) (@lem3228392 A)). Qed.
Lemma lem3228394 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem3228184 A) (@lem3228393 A)). Qed.
Lemma lem3228395 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3228107 A) (@lem3228394 A)). Qed.
