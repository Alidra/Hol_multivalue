Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SET_CASES_term_abbrevs.
Require Import DECOMPOSITION_spec.
Require Import DISJ_ACI_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem3272940 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3272941 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (@lem3272940 (term1 A)). Qed.
Lemma lem3272942 {A : Type'} : (term2 A) = (term1 A).
Proof. exact (SYM (@lem3272941 A)). Qed.
Lemma lem3272943 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3272944 {A : Type'} : term4 A.
Proof. exact (@lem3216368 A). Qed.
Lemma lem3272947 {A : Type'} : term5 A.
Proof. exact (@lem3272928 A). Qed.
Lemma lem3272952 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem3272953 {A : Type'} : term7 A.
Proof. exact (fun h0 : term6 A => @lem3272952 A h0). Qed.
Lemma lem3272954 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem3272955 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem3272956 {A : Type'} (h1 : term6 A) (h2 : term7 A) : term6 A.
Proof. exact (@lem3272954 A h2 (@lem3272955 A h1)). Qed.
Lemma lem3272957 {A : Type'} (h1 : term6 A) : term8 A.
Proof. exact (fun h0 : term7 A => @lem3272956 A h1 h0). Qed.
Lemma lem3272958 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem3272959 {A : Type'} (h1 : term6 A) (h2 : term7 A) : term6 A.
Proof. exact (@lem3272957 A h1 (@lem3272958 A h2)). Qed.
Lemma lem3272960 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (fun h0 : term6 A => @lem3272959 A h0 h1). Qed.
Lemma lem3272961 {A : Type'} : term9 A.
Proof. exact (fun h0 : term7 A => @lem3272960 A h0). Qed.
Lemma lem3272964 {A : Type'} : term7 A.
Proof. exact (@lem3272961 A (@lem3272953 A)). Qed.
Lemma lem3272965 {A : Type'} : term7 A.
Proof. exact (@lem3272964 A). Qed.
Lemma lem3273133 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3273134 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (@lem3273133 (term4 A)). Qed.
Lemma lem3273143 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (eq_refl (term12 A)). Qed.
Lemma lem3273144 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3273143 A) (@lem3273134 A)). Qed.
Lemma lem3273147 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (eq_refl (term15 A)). Qed.
Lemma lem3273154 {A : Type'} : (term6 A) = (term16 A).
Proof. exact (MK_COMB (@lem3273147 A) (@lem3273144 A)). Qed.
Lemma lem3273157 {A : Type'} (s : A -> Prop) : (term17 A s) = (term17 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem3273158 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem3273159 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3273158 A x s)). Qed.
Lemma lem3273160 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3273161 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3273160 A) (@lem3273159 A s)). Qed.
Lemma lem3273162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3273163 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (MK_COMB (@lem3273162) (@lem3273161 A s)). Qed.
Lemma lem3273164 {A : Type'} (s : A -> Prop) : ((term19 A s) = (term17 A s)) = ((term19 A s) = (term17 A s)).
Proof. exact (MK_COMB (@lem3273163 A s) (@lem3273157 A s)). Qed.
Lemma lem3273165 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273164 A s)). Qed.
Lemma lem3273166 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273167 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem3273166 A) (@lem3273165 A)). Qed.
Lemma lem3273168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3273169 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3273168) (@lem3273167 A)). Qed.
Lemma lem3273176 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A s x t) = (term22 A s x t).
Proof. exact (eq_refl (term22 A s x t)). Qed.
Lemma lem3273177 {A : Type'} (s : A -> Prop) (x : A) : (term23 A s x) = (term23 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3273176 A s x t)). Qed.
Lemma lem3273178 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3273179 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term24 A s x).
Proof. exact (MK_COMB (@lem3273178 A) (@lem3273177 A s x)). Qed.
Lemma lem3273182 {A : Type'} (x : A) (s : A -> Prop) : (term25 A x s) = (term25 A x s).
Proof. exact (eq_refl (term25 A x s)). Qed.
Lemma lem3273183 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (term24 A s x)) = ((@IN A x s) = (term24 A s x)).
Proof. exact (MK_COMB (@lem3273182 A x s) (@lem3273179 A s x)). Qed.
Lemma lem3273184 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (fun_ext (fun x : A => @lem3273183 A s x)). Qed.
Lemma lem3273185 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3273186 {A : Type'} (s : A -> Prop) : (term27 A s) = (term27 A s).
Proof. exact (MK_COMB (@lem3273185 A) (@lem3273184 A s)). Qed.
Lemma lem3273187 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273186 A s)). Qed.
Lemma lem3273188 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273189 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem3273188 A) (@lem3273187 A)). Qed.
Lemma lem3273190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3273191 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3273190) (@lem3273189 A)). Qed.
Lemma lem3273192 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (MK_COMB (@lem3273191 A) (@lem3273169 A)). Qed.
Lemma lem3273199 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A s x t) = (term22 A s x t).
Proof. exact (eq_refl (term22 A s x t)). Qed.
Lemma lem3273200 {A : Type'} (s : A -> Prop) (x : A) : (term23 A s x) = (term23 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3273199 A s x t)). Qed.
Lemma lem3273201 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3273202 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term24 A s x).
Proof. exact (MK_COMB (@lem3273201 A) (@lem3273200 A s x)). Qed.
Lemma lem3273203 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (fun_ext (fun x : A => @lem3273202 A s x)). Qed.
Lemma lem3273204 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3273205 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3273204 A) (@lem3273203 A s)). Qed.
Lemma lem3273208 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (eq_refl (term31 A s)). Qed.
Lemma lem3273209 {A : Type'} (s : A -> Prop) : (term32 A s) = (term32 A s).
Proof. exact (MK_COMB (@lem3273208 A s) (@lem3273205 A s)). Qed.
Lemma lem3273210 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273209 A s)). Qed.
Lemma lem3273211 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273212 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (MK_COMB (@lem3273211 A) (@lem3273210 A)). Qed.
Lemma lem3273213 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3273214 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem3273213) (@lem3273212 A)). Qed.
Lemma lem3273215 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3273216 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (MK_COMB (@lem3273215) (@lem3273214 A)). Qed.
Lemma lem3273217 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem3273216 A) (@lem3273192 A)). Qed.
Lemma lem3273278 {A : Type'} : (term6 A) = (term16 A).
Proof. exact (TRANS (@lem3273154 A) (@lem3273217 A)). Qed.
Lemma lem3273279 {A : Type'} : (term16 A) = (term6 A).
Proof. exact (SYM (@lem3273278 A)). Qed.
Lemma lem3273280 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3273281 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem3273282 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem3273287 {A : Type'} (x : A) (t : A -> Prop) : (term34 A x t) = (@IN A x t).
Proof. exact (@lem16933 (@IN A x t)). Qed.
Lemma lem3273289 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A s x t) = (term35 A s x t).
Proof. exact (eq_refl (term35 A s x t)). Qed.
Lemma lem3273290 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term36 A s x t) = (term37 A s x t).
Proof. exact (MK_COMB (@lem3273289 A s x t) (@lem3273287 A x t)). Qed.
Lemma lem3273291 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term38 A s x t) = (term36 A s x t).
Proof. exact (@lem17045 (s = (@INSERT A x t)) (term39 A x t)). Qed.
Lemma lem3273292 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term38 A s x t) = (term37 A s x t).
Proof. exact (TRANS (@lem3273291 A s x t) (@lem3273290 A s x t)). Qed.
Lemma lem3273293 {A : Type'} (P : type686 A) : (term40 A P) = (term41 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3273294 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = (term43 A s x).
Proof. exact (@lem3273293 A (term23 A s x)). Qed.
Lemma lem3273295 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term44 A s x t) = (term22 A s x t).
Proof. exact (eq_refl (term44 A s x t)). Qed.
Lemma lem3273296 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3273297 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term45 A s x t) = (term38 A s x t).
Proof. exact (MK_COMB (@lem3273296) (@lem3273295 A s x t)). Qed.
Lemma lem3273298 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term45 A s x t) = (term37 A s x t).
Proof. exact (TRANS (@lem3273297 A s x t) (@lem3273292 A s x t)). Qed.
Lemma lem3273299 {A : Type'} (s : A -> Prop) (x : A) : (term46 A s x) = (term47 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3273298 A s x t)). Qed.
Lemma lem3273300 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273301 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term48 A s x).
Proof. exact (MK_COMB (@lem3273300 A) (@lem3273299 A s x)). Qed.
Lemma lem3273302 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = (term48 A s x).
Proof. exact (TRANS (@lem3273294 A s x) (@lem3273301 A s x)). Qed.
Lemma lem3273303 {A : Type'} (P : A -> Prop) : (term49 A P) = (term50 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3273304 {A : Type'} (s : A -> Prop) : (term51 A s) = (term52 A s).
Proof. exact (@lem3273303 A (term29 A s)). Qed.
Lemma lem3273305 {A : Type'} (s : A -> Prop) (x : A) : (term53 A s x) = (term24 A s x).
Proof. exact (eq_refl (term53 A s x)). Qed.
Lemma lem3273306 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3273307 {A : Type'} (s : A -> Prop) (x : A) : (term54 A s x) = (term42 A s x).
Proof. exact (MK_COMB (@lem3273306) (@lem3273305 A s x)). Qed.
Lemma lem3273308 {A : Type'} (s : A -> Prop) (x : A) : (term54 A s x) = (term48 A s x).
Proof. exact (TRANS (@lem3273307 A s x) (@lem3273302 A s x)). Qed.
Lemma lem3273309 {A : Type'} (s : A -> Prop) : (term55 A s) = (term56 A s).
Proof. exact (fun_ext (fun x : A => @lem3273308 A s x)). Qed.
Lemma lem3273310 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3273311 {A : Type'} (s : A -> Prop) : (term52 A s) = (term57 A s).
Proof. exact (MK_COMB (@lem3273310 A) (@lem3273309 A s)). Qed.
Lemma lem3273312 {A : Type'} (s : A -> Prop) : (term51 A s) = (term57 A s).
Proof. exact (TRANS (@lem3273304 A s) (@lem3273311 A s)). Qed.
Lemma lem3273314 {A : Type'} (s : A -> Prop) : (term58 A s) = (term58 A s).
Proof. exact (eq_refl (term58 A s)). Qed.
Lemma lem3273315 {A : Type'} (s : A -> Prop) : (term59 A s) = (term60 A s).
Proof. exact (MK_COMB (@lem3273314 A s) (@lem3273312 A s)). Qed.
Lemma lem3273316 {A : Type'} (s : A -> Prop) : (term61 A s) = (term59 A s).
Proof. exact (@lem17160 (s = (@EMPTY A)) (term30 A s)). Qed.
Lemma lem3273317 {A : Type'} (s : A -> Prop) : (term61 A s) = (term60 A s).
Proof. exact (TRANS (@lem3273316 A s) (@lem3273315 A s)). Qed.
Lemma lem3273318 {A : Type'} (P : type686 A) : (term62 A P) = (term63 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3273319 {A : Type'} : (term3 A) = (term64 A).
Proof. exact (@lem3273318 A (term33 A)). Qed.
Lemma lem3273320 {A : Type'} (s : A -> Prop) : (term65 A s) = (term32 A s).
Proof. exact (eq_refl (term65 A s)). Qed.
Lemma lem3273321 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3273322 {A : Type'} (s : A -> Prop) : (term66 A s) = (term61 A s).
Proof. exact (MK_COMB (@lem3273321) (@lem3273320 A s)). Qed.
Lemma lem3273323 {A : Type'} (s : A -> Prop) : (term66 A s) = (term60 A s).
Proof. exact (TRANS (@lem3273322 A s) (@lem3273317 A s)). Qed.
Lemma lem3273324 {A : Type'} : (term67 A) = (term68 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273323 A s)). Qed.
Lemma lem3273325 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3273326 {A : Type'} : (term64 A) = (term69 A).
Proof. exact (MK_COMB (@lem3273325 A) (@lem3273324 A)). Qed.
Lemma lem3273431 {A : Type'} : (term3 A) = (term69 A).
Proof. exact (TRANS (@lem3273319 A) (@lem3273326 A)). Qed.
Lemma lem3273432 {A : Type'} (h1 : term3 A) : term69 A.
Proof. exact (EQ_MP (@lem3273431 A) (@lem3273280 A h1)). Qed.
Lemma lem3273440 {A : Type'} (x : A) (t : A -> Prop) : (term34 A x t) = (@IN A x t).
Proof. exact (@lem16933 (@IN A x t)). Qed.
Lemma lem3273442 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A s x t) = (term35 A s x t).
Proof. exact (eq_refl (term35 A s x t)). Qed.
Lemma lem3273443 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term36 A s x t) = (term37 A s x t).
Proof. exact (MK_COMB (@lem3273442 A s x t) (@lem3273440 A x t)). Qed.
Lemma lem3273444 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term38 A s x t) = (term36 A s x t).
Proof. exact (@lem17045 (s = (@INSERT A x t)) (term39 A x t)). Qed.
Lemma lem3273445 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term38 A s x t) = (term37 A s x t).
Proof. exact (TRANS (@lem3273444 A s x t) (@lem3273443 A s x t)). Qed.
Lemma lem3273448 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A s x t) = (term22 A s x t).
Proof. exact (eq_refl (term22 A s x t)). Qed.
Lemma lem3273449 {A : Type'} (P : type686 A) : (term40 A P) = (term41 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3273450 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = (term43 A s x).
Proof. exact (@lem3273449 A (term23 A s x)). Qed.
Lemma lem3273451 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term44 A s x t) = (term22 A s x t).
Proof. exact (eq_refl (term44 A s x t)). Qed.
Lemma lem3273452 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3273453 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term45 A s x t) = (term38 A s x t).
Proof. exact (MK_COMB (@lem3273452) (@lem3273451 A s x t)). Qed.
Lemma lem3273454 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term45 A s x t) = (term37 A s x t).
Proof. exact (TRANS (@lem3273453 A s x t) (@lem3273445 A s x t)). Qed.
Lemma lem3273455 {A : Type'} (s : A -> Prop) (x : A) : (term46 A s x) = (term47 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3273454 A s x t)). Qed.
Lemma lem3273456 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273457 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term48 A s x).
Proof. exact (MK_COMB (@lem3273456 A) (@lem3273455 A s x)). Qed.
Lemma lem3273458 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = (term48 A s x).
Proof. exact (TRANS (@lem3273450 A s x) (@lem3273457 A s x)). Qed.
Lemma lem3273459 {A : Type'} (s : A -> Prop) (x : A) : (term23 A s x) = (term23 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3273448 A s x t)). Qed.
Lemma lem3273460 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3273461 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term24 A s x).
Proof. exact (MK_COMB (@lem3273460 A) (@lem3273459 A s x)). Qed.
Lemma lem3273463 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term70 A x s).
Proof. exact (eq_refl (term70 A x s)). Qed.
Lemma lem3273464 {A : Type'} (s : A -> Prop) (x : A) : (term71 A s x) = (term71 A s x).
Proof. exact (MK_COMB (@lem3273463 A x s) (@lem3273461 A s x)). Qed.
Lemma lem3273466 {A : Type'} (x : A) (s : A -> Prop) : (term72 A x s) = (term72 A x s).
Proof. exact (eq_refl (term72 A x s)). Qed.
Lemma lem3273467 {A : Type'} (s : A -> Prop) (x : A) : (term73 A s x) = (term74 A s x).
Proof. exact (MK_COMB (@lem3273466 A x s) (@lem3273458 A s x)). Qed.
Lemma lem3273468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3273469 {A : Type'} (s : A -> Prop) (x : A) : (term75 A s x) = (term76 A s x).
Proof. exact (MK_COMB (@lem3273468) (@lem3273467 A s x)). Qed.
Lemma lem3273470 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term78 A s x).
Proof. exact (MK_COMB (@lem3273469 A s x) (@lem3273464 A s x)). Qed.
Lemma lem3273471 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (term24 A s x)) = (term77 A s x).
Proof. exact (@lem17784 (@IN A x s) (term24 A s x)). Qed.
Lemma lem3273472 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (term24 A s x)) = (term78 A s x).
Proof. exact (TRANS (@lem3273471 A s x) (@lem3273470 A s x)). Qed.
Lemma lem3273473 {A : Type'} (s : A -> Prop) : (term26 A s) = (term79 A s).
Proof. exact (fun_ext (fun x : A => @lem3273472 A s x)). Qed.
Lemma lem3273474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3273475 {A : Type'} (s : A -> Prop) : (term27 A s) = (term80 A s).
Proof. exact (MK_COMB (@lem3273474 A) (@lem3273473 A s)). Qed.
Lemma lem3273476 {A : Type'} : (term28 A) = (term81 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273475 A s)). Qed.
Lemma lem3273477 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273478 {A : Type'} : (term5 A) = (term82 A).
Proof. exact (MK_COMB (@lem3273477 A) (@lem3273476 A)). Qed.
Lemma lem3273484 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3273485 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (@lem3273484 A P Q). Qed.
Lemma lem3273486 {A : Type'} (s : A -> Prop) : (term85 A s) = (term86 A s).
Proof. exact (@lem3273485 A (term87 A s) (term88 A s)). Qed.
Lemma lem3273487 {A : Type'} (s : A -> Prop) (x : A) : (term89 A s x) = (term74 A s x).
Proof. exact (eq_refl (term89 A s x)). Qed.
Lemma lem3273488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3273489 {A : Type'} (s : A -> Prop) (x : A) : (term90 A s x) = (term76 A s x).
Proof. exact (MK_COMB (@lem3273488) (@lem3273487 A s x)). Qed.
Lemma lem3273490 {A : Type'} (s : A -> Prop) (x : A) : (term91 A s x) = (term71 A s x).
Proof. exact (eq_refl (term91 A s x)). Qed.
Lemma lem3273491 {A : Type'} (s : A -> Prop) (x : A) : (term92 A s x) = (term78 A s x).
Proof. exact (MK_COMB (@lem3273489 A s x) (@lem3273490 A s x)). Qed.
Lemma lem3273492 {A : Type'} (s : A -> Prop) : (term93 A s) = (term79 A s).
Proof. exact (fun_ext (fun x : A => @lem3273491 A s x)). Qed.
Lemma lem3273493 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3273494 {A : Type'} (s : A -> Prop) : (term85 A s) = (term80 A s).
Proof. exact (MK_COMB (@lem3273493 A) (@lem3273492 A s)). Qed.
Lemma lem3273495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3273496 {A : Type'} (s : A -> Prop) : (term94 A s) = (term95 A s).
Proof. exact (MK_COMB (@lem3273495) (@lem3273494 A s)). Qed.
Lemma lem3273497 {A : Type'} (s : A -> Prop) (x : A) : (term89 A s x) = (term74 A s x).
Proof. exact (eq_refl (term89 A s x)). Qed.
Lemma lem3273498 {A : Type'} (s : A -> Prop) : (term96 A s) = (term87 A s).
Proof. exact (fun_ext (fun x : A => @lem3273497 A s x)). Qed.
Lemma lem3273499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3273500 {A : Type'} (s : A -> Prop) : (term97 A s) = (term98 A s).
Proof. exact (MK_COMB (@lem3273499 A) (@lem3273498 A s)). Qed.
Lemma lem3273501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3273502 {A : Type'} (s : A -> Prop) : (term99 A s) = (term100 A s).
Proof. exact (MK_COMB (@lem3273501) (@lem3273500 A s)). Qed.
Lemma lem3273503 {A : Type'} (s : A -> Prop) (x : A) : (term91 A s x) = (term71 A s x).
Proof. exact (eq_refl (term91 A s x)). Qed.
Lemma lem3273504 {A : Type'} (s : A -> Prop) : (term101 A s) = (term88 A s).
Proof. exact (fun_ext (fun x : A => @lem3273503 A s x)). Qed.
Lemma lem3273505 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3273506 {A : Type'} (s : A -> Prop) : (term102 A s) = (term103 A s).
Proof. exact (MK_COMB (@lem3273505 A) (@lem3273504 A s)). Qed.
Lemma lem3273507 {A : Type'} (s : A -> Prop) : (term86 A s) = (term104 A s).
Proof. exact (MK_COMB (@lem3273502 A s) (@lem3273506 A s)). Qed.
Lemma lem3273508 {A : Type'} (s : A -> Prop) : ((term85 A s) = (term86 A s)) = ((term80 A s) = (term104 A s)).
Proof. exact (MK_COMB (@lem3273496 A s) (@lem3273507 A s)). Qed.
Lemma lem3273509 {A : Type'} (s : A -> Prop) : (term80 A s) = (term104 A s).
Proof. exact (EQ_MP (@lem3273508 A s) (@lem3273486 A s)). Qed.
Lemma lem3273702 {A : Type'} : (term81 A) = (term105 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273509 A s)). Qed.
Lemma lem3273703 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273704 {A : Type'} : (term82 A) = (term106 A).
Proof. exact (MK_COMB (@lem3273703 A) (@lem3273702 A)). Qed.
Lemma lem3273706 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3273707 {A : Type'} (P : type686 A) (Q : type686 A) : (term107 A P Q) = (term108 A P Q).
Proof. exact (@lem3273706 (A -> Prop) P Q). Qed.
Lemma lem3273708 {A : Type'} : (term109 A) = (term110 A).
Proof. exact (@lem3273707 A (term111 A) (term112 A)). Qed.
Lemma lem3273709 {A : Type'} (s : A -> Prop) : (term113 A s) = (term98 A s).
Proof. exact (eq_refl (term113 A s)). Qed.
Lemma lem3273710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3273711 {A : Type'} (s : A -> Prop) : (term114 A s) = (term100 A s).
Proof. exact (MK_COMB (@lem3273710) (@lem3273709 A s)). Qed.
Lemma lem3273712 {A : Type'} (s : A -> Prop) : (term115 A s) = (term103 A s).
Proof. exact (eq_refl (term115 A s)). Qed.
Lemma lem3273713 {A : Type'} (s : A -> Prop) : (term116 A s) = (term104 A s).
Proof. exact (MK_COMB (@lem3273711 A s) (@lem3273712 A s)). Qed.
Lemma lem3273714 {A : Type'} : (term117 A) = (term105 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273713 A s)). Qed.
Lemma lem3273715 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273716 {A : Type'} : (term109 A) = (term106 A).
Proof. exact (MK_COMB (@lem3273715 A) (@lem3273714 A)). Qed.
Lemma lem3273717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3273718 {A : Type'} : (term118 A) = (term119 A).
Proof. exact (MK_COMB (@lem3273717) (@lem3273716 A)). Qed.
Lemma lem3273719 {A : Type'} (s : A -> Prop) : (term113 A s) = (term98 A s).
Proof. exact (eq_refl (term113 A s)). Qed.
Lemma lem3273720 {A : Type'} : (term120 A) = (term111 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273719 A s)). Qed.
Lemma lem3273721 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273722 {A : Type'} : (term121 A) = (term122 A).
Proof. exact (MK_COMB (@lem3273721 A) (@lem3273720 A)). Qed.
Lemma lem3273723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3273724 {A : Type'} : (term123 A) = (term124 A).
Proof. exact (MK_COMB (@lem3273723) (@lem3273722 A)). Qed.
Lemma lem3273725 {A : Type'} (s : A -> Prop) : (term115 A s) = (term103 A s).
Proof. exact (eq_refl (term115 A s)). Qed.
Lemma lem3273726 {A : Type'} : (term125 A) = (term112 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273725 A s)). Qed.
Lemma lem3273727 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273728 {A : Type'} : (term126 A) = (term127 A).
Proof. exact (MK_COMB (@lem3273727 A) (@lem3273726 A)). Qed.
Lemma lem3273729 {A : Type'} : (term110 A) = (term128 A).
Proof. exact (MK_COMB (@lem3273724 A) (@lem3273728 A)). Qed.
Lemma lem3273730 {A : Type'} : ((term109 A) = (term110 A)) = ((term106 A) = (term128 A)).
Proof. exact (MK_COMB (@lem3273718 A) (@lem3273729 A)). Qed.
Lemma lem3273731 {A : Type'} : (term106 A) = (term128 A).
Proof. exact (EQ_MP (@lem3273730 A) (@lem3273708 A)). Qed.
Lemma lem3273932 {A : Type'} : (term82 A) = (term128 A).
Proof. exact (TRANS (@lem3273704 A) (@lem3273731 A)). Qed.
Lemma lem3273934 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3273935 {A : Type'} (P : Prop) (Q : type686 A) : (term131 A P Q) = (term132 A P Q).
Proof. exact (@lem3273934 (A -> Prop) P Q). Qed.
Lemma lem3273936 {A : Type'} (s : A -> Prop) (x : A) : (term133 A s x) = (term134 A s x).
Proof. exact (@lem3273935 A (term39 A x s) (term23 A s x)). Qed.
Lemma lem3273937 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term44 A s x t) = (term22 A s x t).
Proof. exact (eq_refl (term44 A s x t)). Qed.
Lemma lem3273938 {A : Type'} (s : A -> Prop) (x : A) : (term135 A s x) = (term23 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3273937 A s x t)). Qed.
Lemma lem3273939 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3273940 {A : Type'} (s : A -> Prop) (x : A) : (term136 A s x) = (term24 A s x).
Proof. exact (MK_COMB (@lem3273939 A) (@lem3273938 A s x)). Qed.
Lemma lem3273941 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term70 A x s).
Proof. exact (eq_refl (term70 A x s)). Qed.
Lemma lem3273942 {A : Type'} (s : A -> Prop) (x : A) : (term133 A s x) = (term71 A s x).
Proof. exact (MK_COMB (@lem3273941 A x s) (@lem3273940 A s x)). Qed.
Lemma lem3273943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3273944 {A : Type'} (s : A -> Prop) (x : A) : (term137 A s x) = (term138 A s x).
Proof. exact (MK_COMB (@lem3273943) (@lem3273942 A s x)). Qed.
Lemma lem3273945 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term44 A s x t) = (term22 A s x t).
Proof. exact (eq_refl (term44 A s x t)). Qed.
Lemma lem3273946 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term70 A x s).
Proof. exact (eq_refl (term70 A x s)). Qed.
Lemma lem3273947 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term139 A s x t) = (term140 A s x t).
Proof. exact (MK_COMB (@lem3273946 A x s) (@lem3273945 A s x t)). Qed.
Lemma lem3273948 {A : Type'} (s : A -> Prop) (x : A) : (term141 A s x) = (term142 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3273947 A s x t)). Qed.
Lemma lem3273949 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3273950 {A : Type'} (s : A -> Prop) (x : A) : (term134 A s x) = (term143 A s x).
Proof. exact (MK_COMB (@lem3273949 A) (@lem3273948 A s x)). Qed.
Lemma lem3273951 {A : Type'} (s : A -> Prop) (x : A) : ((term133 A s x) = (term134 A s x)) = ((term71 A s x) = (term143 A s x)).
Proof. exact (MK_COMB (@lem3273944 A s x) (@lem3273950 A s x)). Qed.
Lemma lem3273952 {A : Type'} (s : A -> Prop) (x : A) : (term71 A s x) = (term143 A s x).
Proof. exact (EQ_MP (@lem3273951 A s x) (@lem3273936 A s x)). Qed.
Lemma lem3273953 {A : Type'} (s : A -> Prop) : (term88 A s) = (term144 A s).
Proof. exact (fun_ext (fun x : A => @lem3273952 A s x)). Qed.
Lemma lem3273954 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3273955 {A : Type'} (s : A -> Prop) : (term103 A s) = (term145 A s).
Proof. exact (MK_COMB (@lem3273954 A) (@lem3273953 A s)). Qed.
Lemma lem3273957 {A B : Type'} (P : type1413 A B) : (term146 A B P) = (term147 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3273958 {A : Type'} (P : type1364 A) : (term148 A P) = (term149 A P).
Proof. exact (@lem3273957 A (A -> Prop) P). Qed.
Lemma lem3273959 {A : Type'} (s : A -> Prop) : (term150 A s) = (term151 A s).
Proof. exact (@lem3273958 A (term152 A s)). Qed.
Lemma lem3273960 {A : Type'} (s : A -> Prop) (x : A) : (term153 A s x) = (term142 A s x).
Proof. exact (eq_refl (term153 A s x)). Qed.
Lemma lem3273961 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3273962 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term154 A s x t) = (term155 A s x t).
Proof. exact (MK_COMB (@lem3273960 A s x) (@lem3273961 A t)). Qed.
Lemma lem3273963 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term155 A s x t) = (term140 A s x t).
Proof. exact (eq_refl (term155 A s x t)). Qed.
Lemma lem3273964 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term154 A s x t) = (term140 A s x t).
Proof. exact (TRANS (@lem3273962 A s x t) (@lem3273963 A s x t)). Qed.
Lemma lem3273965 {A : Type'} (s : A -> Prop) (x : A) : (term156 A s x) = (term142 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3273964 A s x t)). Qed.
Lemma lem3273966 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3273967 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (term143 A s x).
Proof. exact (MK_COMB (@lem3273966 A) (@lem3273965 A s x)). Qed.
Lemma lem3273968 {A : Type'} (s : A -> Prop) : (term158 A s) = (term144 A s).
Proof. exact (fun_ext (fun x : A => @lem3273967 A s x)). Qed.
Lemma lem3273969 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3273970 {A : Type'} (s : A -> Prop) : (term150 A s) = (term145 A s).
Proof. exact (MK_COMB (@lem3273969 A) (@lem3273968 A s)). Qed.
Lemma lem3273971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3273972 {A : Type'} (s : A -> Prop) : (term159 A s) = (term160 A s).
Proof. exact (MK_COMB (@lem3273971) (@lem3273970 A s)). Qed.
Lemma lem3273973 {A : Type'} (s : A -> Prop) (x : A) : (term153 A s x) = (term142 A s x).
Proof. exact (eq_refl (term153 A s x)). Qed.
Lemma lem3273974 {A : Type'} (t : type1402 A) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3273975 {A : Type'} (s : A -> Prop) (t : type1402 A) (x : A) : (term161 A s t x) = (term162 A s t x).
Proof. exact (MK_COMB (@lem3273973 A s x) (@lem3273974 A t x)). Qed.
Lemma lem3273976 {A : Type'} (s : A -> Prop) (t : type1402 A) (x : A) : (term162 A s t x) = (term163 A s t x).
Proof. exact (eq_refl (term162 A s t x)). Qed.
Lemma lem3273977 {A : Type'} (s : A -> Prop) (t : type1402 A) (x : A) : (term161 A s t x) = (term163 A s t x).
Proof. exact (TRANS (@lem3273975 A s t x) (@lem3273976 A s t x)). Qed.
Lemma lem3273978 {A : Type'} (s : A -> Prop) (t : type1402 A) : (term164 A s t) = (term165 A s t).
Proof. exact (fun_ext (fun x : A => @lem3273977 A s t x)). Qed.
Lemma lem3273979 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3273980 {A : Type'} (s : A -> Prop) (t : type1402 A) : (term166 A s t) = (term167 A s t).
Proof. exact (MK_COMB (@lem3273979 A) (@lem3273978 A s t)). Qed.
Lemma lem3273981 {A : Type'} (s : A -> Prop) : (term168 A s) = (term169 A s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3273980 A s t)). Qed.
Lemma lem3273982 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3273983 {A : Type'} (s : A -> Prop) : (term151 A s) = (term170 A s).
Proof. exact (MK_COMB (@lem3273982 A) (@lem3273981 A s)). Qed.
Lemma lem3273984 {A : Type'} (s : A -> Prop) : ((term150 A s) = (term151 A s)) = ((term145 A s) = (term170 A s)).
Proof. exact (MK_COMB (@lem3273972 A s) (@lem3273983 A s)). Qed.
Lemma lem3273985 {A : Type'} (s : A -> Prop) : (term145 A s) = (term170 A s).
Proof. exact (EQ_MP (@lem3273984 A s) (@lem3273959 A s)). Qed.
Lemma lem3273986 {A : Type'} (s : A -> Prop) : (term103 A s) = (term170 A s).
Proof. exact (TRANS (@lem3273955 A s) (@lem3273985 A s)). Qed.
Lemma lem3273987 {A : Type'} : (term112 A) = (term171 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3273986 A s)). Qed.
Lemma lem3273988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3273989 {A : Type'} : (term127 A) = (term172 A).
Proof. exact (MK_COMB (@lem3273988 A) (@lem3273987 A)). Qed.
Lemma lem3273991 {A B : Type'} (P : type1413 A B) : (term146 A B P) = (term147 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3273992 {A : Type'} (P : type611 A) : (term173 A P) = (term174 A P).
Proof. exact (@lem3273991 (A -> Prop) (type1402 A) P). Qed.
Lemma lem3273993 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (@lem3273992 A (term177 A)). Qed.
Lemma lem3273994 {A : Type'} (s : A -> Prop) : (term178 A s) = (term169 A s).
Proof. exact (eq_refl (term178 A s)). Qed.
Lemma lem3273995 {A : Type'} (t : type1402 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3273996 {A : Type'} (s : A -> Prop) (t : type1402 A) : (term179 A s t) = (term180 A s t).
Proof. exact (MK_COMB (@lem3273994 A s) (@lem3273995 A t)). Qed.
Lemma lem3273997 {A : Type'} (s : A -> Prop) (t : type1402 A) : (term180 A s t) = (term167 A s t).
Proof. exact (eq_refl (term180 A s t)). Qed.
Lemma lem3273998 {A : Type'} (s : A -> Prop) (t : type1402 A) : (term179 A s t) = (term167 A s t).
Proof. exact (TRANS (@lem3273996 A s t) (@lem3273997 A s t)). Qed.
Lemma lem3273999 {A : Type'} (s : A -> Prop) : (term181 A s) = (term169 A s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3273998 A s t)). Qed.
Lemma lem3274000 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3274001 {A : Type'} (s : A -> Prop) : (term182 A s) = (term170 A s).
Proof. exact (MK_COMB (@lem3274000 A) (@lem3273999 A s)). Qed.
Lemma lem3274002 {A : Type'} : (term183 A) = (term171 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274001 A s)). Qed.
Lemma lem3274003 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274004 {A : Type'} : (term175 A) = (term172 A).
Proof. exact (MK_COMB (@lem3274003 A) (@lem3274002 A)). Qed.
Lemma lem3274005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3274006 {A : Type'} : (term184 A) = (term185 A).
Proof. exact (MK_COMB (@lem3274005) (@lem3274004 A)). Qed.
Lemma lem3274007 {A : Type'} (s : A -> Prop) : (term178 A s) = (term169 A s).
Proof. exact (eq_refl (term178 A s)). Qed.
Lemma lem3274008 {A : Type'} (t : type667 A) (s : A -> Prop) : (t s) = (t s).
Proof. exact (eq_refl (t s)). Qed.
Lemma lem3274009 {A : Type'} (t : type667 A) (s : A -> Prop) : (term186 A t s) = (term187 A t s).
Proof. exact (MK_COMB (@lem3274007 A s) (@lem3274008 A t s)). Qed.
Lemma lem3274010 {A : Type'} (t : type667 A) (s : A -> Prop) : (term187 A t s) = (term188 A t s).
Proof. exact (eq_refl (term187 A t s)). Qed.
Lemma lem3274011 {A : Type'} (t : type667 A) (s : A -> Prop) : (term186 A t s) = (term188 A t s).
Proof. exact (TRANS (@lem3274009 A t s) (@lem3274010 A t s)). Qed.
Lemma lem3274012 {A : Type'} (t : type667 A) : (term189 A t) = (term190 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274011 A t s)). Qed.
Lemma lem3274013 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274014 {A : Type'} (t : type667 A) : (term191 A t) = (term192 A t).
Proof. exact (MK_COMB (@lem3274013 A) (@lem3274012 A t)). Qed.
Lemma lem3274015 {A : Type'} : (term193 A) = (term194 A).
Proof. exact (fun_ext (fun t : type667 A => @lem3274014 A t)). Qed.
Lemma lem3274016 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem3274017 {A : Type'} : (term176 A) = (term195 A).
Proof. exact (MK_COMB (@lem3274016 A) (@lem3274015 A)). Qed.
Lemma lem3274018 {A : Type'} : ((term175 A) = (term176 A)) = ((term172 A) = (term195 A)).
Proof. exact (MK_COMB (@lem3274006 A) (@lem3274017 A)). Qed.
Lemma lem3274019 {A : Type'} : (term172 A) = (term195 A).
Proof. exact (EQ_MP (@lem3274018 A) (@lem3273993 A)). Qed.
Lemma lem3274020 {A : Type'} : (term127 A) = (term195 A).
Proof. exact (TRANS (@lem3273989 A) (@lem3274019 A)). Qed.
Lemma lem3274021 {A : Type'} : (term124 A) = (term124 A).
Proof. exact (eq_refl (term124 A)). Qed.
Lemma lem3274022 {A : Type'} : (term128 A) = (term196 A).
Proof. exact (MK_COMB (@lem3274021 A) (@lem3274020 A)). Qed.
Lemma lem3274024 {A : Type'} (P : Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3274025 {A : Type'} (P : Prop) (Q : type149 A) : (term199 A P Q) = (term200 A P Q).
Proof. exact (@lem3274024 (type667 A) P Q). Qed.
Lemma lem3274026 {A : Type'} : (term201 A) = (term202 A).
Proof. exact (@lem3274025 A (term122 A) (term194 A)). Qed.
Lemma lem3274027 {A : Type'} (t : type667 A) : (term203 A t) = (term192 A t).
Proof. exact (eq_refl (term203 A t)). Qed.
Lemma lem3274028 {A : Type'} : (term204 A) = (term194 A).
Proof. exact (fun_ext (fun t : type667 A => @lem3274027 A t)). Qed.
Lemma lem3274029 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem3274030 {A : Type'} : (term205 A) = (term195 A).
Proof. exact (MK_COMB (@lem3274029 A) (@lem3274028 A)). Qed.
Lemma lem3274031 {A : Type'} : (term124 A) = (term124 A).
Proof. exact (eq_refl (term124 A)). Qed.
Lemma lem3274032 {A : Type'} : (term201 A) = (term196 A).
Proof. exact (MK_COMB (@lem3274031 A) (@lem3274030 A)). Qed.
Lemma lem3274033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3274034 {A : Type'} : (term206 A) = (term207 A).
Proof. exact (MK_COMB (@lem3274033) (@lem3274032 A)). Qed.
Lemma lem3274035 {A : Type'} (t : type667 A) : (term203 A t) = (term192 A t).
Proof. exact (eq_refl (term203 A t)). Qed.
Lemma lem3274036 {A : Type'} : (term124 A) = (term124 A).
Proof. exact (eq_refl (term124 A)). Qed.
Lemma lem3274037 {A : Type'} (t : type667 A) : (term208 A t) = (term209 A t).
Proof. exact (MK_COMB (@lem3274036 A) (@lem3274035 A t)). Qed.
Lemma lem3274038 {A : Type'} : (term210 A) = (term211 A).
Proof. exact (fun_ext (fun t : type667 A => @lem3274037 A t)). Qed.
Lemma lem3274039 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem3274040 {A : Type'} : (term202 A) = (term212 A).
Proof. exact (MK_COMB (@lem3274039 A) (@lem3274038 A)). Qed.
Lemma lem3274041 {A : Type'} : ((term201 A) = (term202 A)) = ((term196 A) = (term212 A)).
Proof. exact (MK_COMB (@lem3274034 A) (@lem3274040 A)). Qed.
Lemma lem3274042 {A : Type'} : (term196 A) = (term212 A).
Proof. exact (EQ_MP (@lem3274041 A) (@lem3274026 A)). Qed.
Lemma lem3274043 {A : Type'} : (term128 A) = (term212 A).
Proof. exact (TRANS (@lem3274022 A) (@lem3274042 A)). Qed.
Lemma lem3274044 {A : Type'} : (term82 A) = (term212 A).
Proof. exact (TRANS (@lem3273932 A) (@lem3274043 A)). Qed.
Lemma lem3274045 {A : Type'} : (term5 A) = (term212 A).
Proof. exact (TRANS (@lem3273478 A) (@lem3274044 A)). Qed.
Lemma lem3274046 {A : Type'} (h1 : term5 A) : term212 A.
Proof. exact (EQ_MP (@lem3274045 A) (@lem3273281 A h1)). Qed.
Lemma lem3274048 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem3274049 {A : Type'} (P : A -> Prop) : (term49 A P) = (term50 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3274050 {A : Type'} (s : A -> Prop) : (term213 A s) = (term214 A s).
Proof. exact (@lem3274049 A (term18 A s)). Qed.
Lemma lem3274051 {A : Type'} (x : A) (s : A -> Prop) : (term215 A s x) = (@IN A x s).
Proof. exact (eq_refl (term215 A s x)). Qed.
Lemma lem3274052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3274054 {A : Type'} (x : A) (s : A -> Prop) : (term216 A s x) = (term39 A x s).
Proof. exact (MK_COMB (@lem3274052) (@lem3274051 A x s)). Qed.
Lemma lem3274055 {A : Type'} (s : A -> Prop) : (term217 A s) = (term218 A s).
Proof. exact (fun_ext (fun x : A => @lem3274054 A x s)). Qed.
Lemma lem3274056 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3274057 {A : Type'} (s : A -> Prop) : (term214 A s) = (term219 A s).
Proof. exact (MK_COMB (@lem3274056 A) (@lem3274055 A s)). Qed.
Lemma lem3274058 {A : Type'} (s : A -> Prop) : (term213 A s) = (term219 A s).
Proof. exact (TRANS (@lem3274050 A s) (@lem3274057 A s)). Qed.
Lemma lem3274059 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3274048 A x s)). Qed.
Lemma lem3274060 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3274061 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3274060 A) (@lem3274059 A s)). Qed.
Lemma lem3274062 {A : Type'} (s : A -> Prop) : (term17 A s) = (term17 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem3274065 {A : Type'} (s : A -> Prop) : (term220 A s) = (s = (@EMPTY A)).
Proof. exact (@lem16933 (s = (@EMPTY A))). Qed.
Lemma lem3274066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3274067 {A : Type'} (s : A -> Prop) : (term221 A s) = (term222 A s).
Proof. exact (MK_COMB (@lem3274066) (@lem3274058 A s)). Qed.
Lemma lem3274068 {A : Type'} (s : A -> Prop) : (term223 A s) = (term224 A s).
Proof. exact (MK_COMB (@lem3274067 A s) (@lem3274062 A s)). Qed.
Lemma lem3274069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3274070 {A : Type'} (s : A -> Prop) : (term225 A s) = (term225 A s).
Proof. exact (MK_COMB (@lem3274069) (@lem3274061 A s)). Qed.
Lemma lem3274071 {A : Type'} (s : A -> Prop) : (term226 A s) = (term227 A s).
Proof. exact (MK_COMB (@lem3274070 A s) (@lem3274065 A s)). Qed.
Lemma lem3274072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3274073 {A : Type'} (s : A -> Prop) : (term228 A s) = (term229 A s).
Proof. exact (MK_COMB (@lem3274072) (@lem3274071 A s)). Qed.
Lemma lem3274074 {A : Type'} (s : A -> Prop) : (term230 A s) = (term231 A s).
Proof. exact (MK_COMB (@lem3274073 A s) (@lem3274068 A s)). Qed.
Lemma lem3274075 {A : Type'} (s : A -> Prop) : ((term19 A s) = (term17 A s)) = (term230 A s).
Proof. exact (@lem17784 (term19 A s) (term17 A s)). Qed.
Lemma lem3274076 {A : Type'} (s : A -> Prop) : ((term19 A s) = (term17 A s)) = (term231 A s).
Proof. exact (TRANS (@lem3274075 A s) (@lem3274074 A s)). Qed.
Lemma lem3274077 {A : Type'} : (term21 A) = (term232 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274076 A s)). Qed.
Lemma lem3274078 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274079 {A : Type'} : (term4 A) = (term233 A).
Proof. exact (MK_COMB (@lem3274078 A) (@lem3274077 A)). Qed.
Lemma lem3274081 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3274082 {A : Type'} (P : type686 A) (Q : type686 A) : (term107 A P Q) = (term108 A P Q).
Proof. exact (@lem3274081 (A -> Prop) P Q). Qed.
Lemma lem3274083 {A : Type'} : (term234 A) = (term235 A).
Proof. exact (@lem3274082 A (term236 A) (term237 A)). Qed.
Lemma lem3274084 {A : Type'} (s : A -> Prop) : (term238 A s) = (term227 A s).
Proof. exact (eq_refl (term238 A s)). Qed.
Lemma lem3274085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3274086 {A : Type'} (s : A -> Prop) : (term239 A s) = (term229 A s).
Proof. exact (MK_COMB (@lem3274085) (@lem3274084 A s)). Qed.
Lemma lem3274087 {A : Type'} (s : A -> Prop) : (term240 A s) = (term224 A s).
Proof. exact (eq_refl (term240 A s)). Qed.
Lemma lem3274088 {A : Type'} (s : A -> Prop) : (term241 A s) = (term231 A s).
Proof. exact (MK_COMB (@lem3274086 A s) (@lem3274087 A s)). Qed.
Lemma lem3274089 {A : Type'} : (term242 A) = (term232 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274088 A s)). Qed.
Lemma lem3274090 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274091 {A : Type'} : (term234 A) = (term233 A).
Proof. exact (MK_COMB (@lem3274090 A) (@lem3274089 A)). Qed.
Lemma lem3274092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3274093 {A : Type'} : (term243 A) = (term244 A).
Proof. exact (MK_COMB (@lem3274092) (@lem3274091 A)). Qed.
Lemma lem3274094 {A : Type'} (s : A -> Prop) : (term238 A s) = (term227 A s).
Proof. exact (eq_refl (term238 A s)). Qed.
Lemma lem3274095 {A : Type'} : (term245 A) = (term236 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274094 A s)). Qed.
Lemma lem3274096 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274097 {A : Type'} : (term246 A) = (term247 A).
Proof. exact (MK_COMB (@lem3274096 A) (@lem3274095 A)). Qed.
Lemma lem3274098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3274099 {A : Type'} : (term248 A) = (term249 A).
Proof. exact (MK_COMB (@lem3274098) (@lem3274097 A)). Qed.
Lemma lem3274100 {A : Type'} (s : A -> Prop) : (term240 A s) = (term224 A s).
Proof. exact (eq_refl (term240 A s)). Qed.
Lemma lem3274101 {A : Type'} : (term250 A) = (term237 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274100 A s)). Qed.
Lemma lem3274102 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274103 {A : Type'} : (term251 A) = (term252 A).
Proof. exact (MK_COMB (@lem3274102 A) (@lem3274101 A)). Qed.
Lemma lem3274104 {A : Type'} : (term235 A) = (term253 A).
Proof. exact (MK_COMB (@lem3274099 A) (@lem3274103 A)). Qed.
Lemma lem3274105 {A : Type'} : ((term234 A) = (term235 A)) = ((term233 A) = (term253 A)).
Proof. exact (MK_COMB (@lem3274093 A) (@lem3274104 A)). Qed.
Lemma lem3274106 {A : Type'} : (term233 A) = (term253 A).
Proof. exact (EQ_MP (@lem3274105 A) (@lem3274083 A)). Qed.
Lemma lem3274212 {A : Type'} (P : A -> Prop) (Q : Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3274213 {A : Type'} (P : A -> Prop) (Q : Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (@lem3274212 A P Q). Qed.
Lemma lem3274214 {A : Type'} (s : A -> Prop) : (term256 A s) = (term257 A s).
Proof. exact (@lem3274213 A (term18 A s) (s = (@EMPTY A))). Qed.
Lemma lem3274215 {A : Type'} (x : A) (s : A -> Prop) : (term215 A s x) = (@IN A x s).
Proof. exact (eq_refl (term215 A s x)). Qed.
Lemma lem3274216 {A : Type'} (s : A -> Prop) : (term258 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3274215 A x s)). Qed.
Lemma lem3274217 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3274218 {A : Type'} (s : A -> Prop) : (term259 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3274217 A) (@lem3274216 A s)). Qed.
Lemma lem3274219 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3274220 {A : Type'} (s : A -> Prop) : (term260 A s) = (term225 A s).
Proof. exact (MK_COMB (@lem3274219) (@lem3274218 A s)). Qed.
Lemma lem3274221 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem3274222 {A : Type'} (s : A -> Prop) : (term256 A s) = (term227 A s).
Proof. exact (MK_COMB (@lem3274220 A s) (@lem3274221 A s)). Qed.
Lemma lem3274223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3274224 {A : Type'} (s : A -> Prop) : (term261 A s) = (term262 A s).
Proof. exact (MK_COMB (@lem3274223) (@lem3274222 A s)). Qed.
Lemma lem3274225 {A : Type'} (x : A) (s : A -> Prop) : (term215 A s x) = (@IN A x s).
Proof. exact (eq_refl (term215 A s x)). Qed.
Lemma lem3274226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3274227 {A : Type'} (x : A) (s : A -> Prop) : (term263 A s x) = (term72 A x s).
Proof. exact (MK_COMB (@lem3274226) (@lem3274225 A x s)). Qed.
Lemma lem3274228 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem3274229 {A : Type'} (x : A) (s : A -> Prop) : (term264 A x s) = (term265 A x s).
Proof. exact (MK_COMB (@lem3274227 A x s) (@lem3274228 A s)). Qed.
Lemma lem3274230 {A : Type'} (s : A -> Prop) : (term266 A s) = (term267 A s).
Proof. exact (fun_ext (fun x : A => @lem3274229 A x s)). Qed.
Lemma lem3274231 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3274232 {A : Type'} (s : A -> Prop) : (term257 A s) = (term268 A s).
Proof. exact (MK_COMB (@lem3274231 A) (@lem3274230 A s)). Qed.
Lemma lem3274233 {A : Type'} (s : A -> Prop) : ((term256 A s) = (term257 A s)) = ((term227 A s) = (term268 A s)).
Proof. exact (MK_COMB (@lem3274224 A s) (@lem3274232 A s)). Qed.
Lemma lem3274234 {A : Type'} (s : A -> Prop) : (term227 A s) = (term268 A s).
Proof. exact (EQ_MP (@lem3274233 A s) (@lem3274214 A s)). Qed.
Lemma lem3274235 {A : Type'} : (term236 A) = (term269 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274234 A s)). Qed.
Lemma lem3274236 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274237 {A : Type'} : (term247 A) = (term270 A).
Proof. exact (MK_COMB (@lem3274236 A) (@lem3274235 A)). Qed.
Lemma lem3274239 {A B : Type'} (P : type1413 A B) : (term146 A B P) = (term147 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3274240 {A : Type'} (P : type672 A) : (term271 A P) = (term272 A P).
Proof. exact (@lem3274239 (A -> Prop) A P). Qed.
Lemma lem3274241 {A : Type'} : (term273 A) = (term274 A).
Proof. exact (@lem3274240 A (term275 A)). Qed.
Lemma lem3274242 {A : Type'} (s : A -> Prop) : (term276 A s) = (term267 A s).
Proof. exact (eq_refl (term276 A s)). Qed.
Lemma lem3274243 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3274244 {A : Type'} (s : A -> Prop) (x : A) : (term277 A s x) = (term278 A s x).
Proof. exact (MK_COMB (@lem3274242 A s) (@lem3274243 A x)). Qed.
Lemma lem3274245 {A : Type'} (x : A) (s : A -> Prop) : (term278 A s x) = (term265 A x s).
Proof. exact (eq_refl (term278 A s x)). Qed.
Lemma lem3274246 {A : Type'} (x : A) (s : A -> Prop) : (term277 A s x) = (term265 A x s).
Proof. exact (TRANS (@lem3274244 A s x) (@lem3274245 A x s)). Qed.
Lemma lem3274247 {A : Type'} (s : A -> Prop) : (term279 A s) = (term267 A s).
Proof. exact (fun_ext (fun x : A => @lem3274246 A x s)). Qed.
Lemma lem3274248 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3274249 {A : Type'} (s : A -> Prop) : (term280 A s) = (term268 A s).
Proof. exact (MK_COMB (@lem3274248 A) (@lem3274247 A s)). Qed.
Lemma lem3274250 {A : Type'} : (term281 A) = (term269 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274249 A s)). Qed.
Lemma lem3274251 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274252 {A : Type'} : (term273 A) = (term270 A).
Proof. exact (MK_COMB (@lem3274251 A) (@lem3274250 A)). Qed.
Lemma lem3274253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3274254 {A : Type'} : (term282 A) = (term283 A).
Proof. exact (MK_COMB (@lem3274253) (@lem3274252 A)). Qed.
Lemma lem3274255 {A : Type'} (s : A -> Prop) : (term276 A s) = (term267 A s).
Proof. exact (eq_refl (term276 A s)). Qed.
Lemma lem3274256 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3274257 {A : Type'} (x : type684 A) (s : A -> Prop) : (term284 A x s) = (term285 A x s).
Proof. exact (MK_COMB (@lem3274255 A s) (@lem3274256 A x s)). Qed.
Lemma lem3274258 {A : Type'} (x : type684 A) (s : A -> Prop) : (term285 A x s) = (term286 A x s).
Proof. exact (eq_refl (term285 A x s)). Qed.
Lemma lem3274259 {A : Type'} (x : type684 A) (s : A -> Prop) : (term284 A x s) = (term286 A x s).
Proof. exact (TRANS (@lem3274257 A x s) (@lem3274258 A x s)). Qed.
Lemma lem3274260 {A : Type'} (x : type684 A) : (term287 A x) = (term288 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274259 A x s)). Qed.
Lemma lem3274261 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274262 {A : Type'} (x : type684 A) : (term289 A x) = (term290 A x).
Proof. exact (MK_COMB (@lem3274261 A) (@lem3274260 A x)). Qed.
Lemma lem3274263 {A : Type'} : (term291 A) = (term292 A).
Proof. exact (fun_ext (fun x : type684 A => @lem3274262 A x)). Qed.
Lemma lem3274264 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3274265 {A : Type'} : (term274 A) = (term293 A).
Proof. exact (MK_COMB (@lem3274264 A) (@lem3274263 A)). Qed.
Lemma lem3274266 {A : Type'} : ((term273 A) = (term274 A)) = ((term270 A) = (term293 A)).
Proof. exact (MK_COMB (@lem3274254 A) (@lem3274265 A)). Qed.
Lemma lem3274267 {A : Type'} : (term270 A) = (term293 A).
Proof. exact (EQ_MP (@lem3274266 A) (@lem3274241 A)). Qed.
Lemma lem3274268 {A : Type'} : (term247 A) = (term293 A).
Proof. exact (TRANS (@lem3274237 A) (@lem3274267 A)). Qed.
Lemma lem3274269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3274270 {A : Type'} : (term249 A) = (term294 A).
Proof. exact (MK_COMB (@lem3274269) (@lem3274268 A)). Qed.
Lemma lem3274271 {A : Type'} : (term252 A) = (term252 A).
Proof. exact (eq_refl (term252 A)). Qed.
Lemma lem3274272 {A : Type'} : (term253 A) = (term295 A).
Proof. exact (MK_COMB (@lem3274270 A) (@lem3274271 A)). Qed.
Lemma lem3274274 {A : Type'} (P : A -> Prop) (Q : Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3274275 {A : Type'} (P : type162 A) (Q : Prop) : (term298 A P Q) = (term299 A P Q).
Proof. exact (@lem3274274 (type684 A) P Q). Qed.
Lemma lem3274276 {A : Type'} : (term300 A) = (term301 A).
Proof. exact (@lem3274275 A (term292 A) (term252 A)). Qed.
Lemma lem3274277 {A : Type'} (x : type684 A) : (term302 A x) = (term290 A x).
Proof. exact (eq_refl (term302 A x)). Qed.
Lemma lem3274278 {A : Type'} : (term303 A) = (term292 A).
Proof. exact (fun_ext (fun x : type684 A => @lem3274277 A x)). Qed.
Lemma lem3274279 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3274280 {A : Type'} : (term304 A) = (term293 A).
Proof. exact (MK_COMB (@lem3274279 A) (@lem3274278 A)). Qed.
Lemma lem3274281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3274282 {A : Type'} : (term305 A) = (term294 A).
Proof. exact (MK_COMB (@lem3274281) (@lem3274280 A)). Qed.
Lemma lem3274283 {A : Type'} : (term252 A) = (term252 A).
Proof. exact (eq_refl (term252 A)). Qed.
Lemma lem3274284 {A : Type'} : (term300 A) = (term295 A).
Proof. exact (MK_COMB (@lem3274282 A) (@lem3274283 A)). Qed.
Lemma lem3274285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3274286 {A : Type'} : (term306 A) = (term307 A).
Proof. exact (MK_COMB (@lem3274285) (@lem3274284 A)). Qed.
Lemma lem3274287 {A : Type'} (x : type684 A) : (term302 A x) = (term290 A x).
Proof. exact (eq_refl (term302 A x)). Qed.
Lemma lem3274288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3274289 {A : Type'} (x : type684 A) : (term308 A x) = (term309 A x).
Proof. exact (MK_COMB (@lem3274288) (@lem3274287 A x)). Qed.
Lemma lem3274290 {A : Type'} : (term252 A) = (term252 A).
Proof. exact (eq_refl (term252 A)). Qed.
Lemma lem3274291 {A : Type'} (x : type684 A) : (term310 A x) = (term311 A x).
Proof. exact (MK_COMB (@lem3274289 A x) (@lem3274290 A)). Qed.
Lemma lem3274292 {A : Type'} : (term312 A) = (term313 A).
Proof. exact (fun_ext (fun x : type684 A => @lem3274291 A x)). Qed.
Lemma lem3274293 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3274294 {A : Type'} : (term301 A) = (term314 A).
Proof. exact (MK_COMB (@lem3274293 A) (@lem3274292 A)). Qed.
Lemma lem3274295 {A : Type'} : ((term300 A) = (term301 A)) = ((term295 A) = (term314 A)).
Proof. exact (MK_COMB (@lem3274286 A) (@lem3274294 A)). Qed.
Lemma lem3274296 {A : Type'} : (term295 A) = (term314 A).
Proof. exact (EQ_MP (@lem3274295 A) (@lem3274276 A)). Qed.
Lemma lem3274297 {A : Type'} : (term253 A) = (term314 A).
Proof. exact (TRANS (@lem3274272 A) (@lem3274296 A)). Qed.
Lemma lem3274298 {A : Type'} : (term233 A) = (term314 A).
Proof. exact (TRANS (@lem3274106 A) (@lem3274297 A)). Qed.
Lemma lem3274299 {A : Type'} : (term4 A) = (term314 A).
Proof. exact (TRANS (@lem3274079 A) (@lem3274298 A)). Qed.
Lemma lem3274300 {A : Type'} (h1 : term4 A) : term314 A.
Proof. exact (EQ_MP (@lem3274299 A) (@lem3273282 A h1)). Qed.
Lemma lem3274301 {A : Type'} (x : type684 A) (h1 : term311 A x) : term311 A x.
Proof. exact (h1). Qed.
Lemma lem3274302 {A : Type'} (t : type667 A) (h1 : term209 A t) : term209 A t.
Proof. exact (h1). Qed.
Lemma lem3274303 {A : Type'} (s : A -> Prop) (h1 : term60 A s) : term60 A s.
Proof. exact (h1). Qed.
Lemma lem3274310 {A : Type'} (s : A -> Prop) : (term17 A s) = (term17 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem3274317 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term39 A x s).
Proof. exact (eq_refl (term39 A x s)). Qed.
Lemma lem3274318 {A : Type'} (s : A -> Prop) : (term218 A s) = (term218 A s).
Proof. exact (fun_ext (fun x : A => @lem3274317 A x s)). Qed.
Lemma lem3274319 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3274320 {A : Type'} (s : A -> Prop) : (term219 A s) = (term219 A s).
Proof. exact (MK_COMB (@lem3274319 A) (@lem3274318 A s)). Qed.
Lemma lem3274321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3274322 {A : Type'} (s : A -> Prop) : (term222 A s) = (term222 A s).
Proof. exact (MK_COMB (@lem3274321) (@lem3274320 A s)). Qed.
Lemma lem3274323 {A : Type'} (s : A -> Prop) : (term224 A s) = (term224 A s).
Proof. exact (MK_COMB (@lem3274322 A s) (@lem3274310 A s)). Qed.
Lemma lem3274324 {A : Type'} : (term237 A) = (term237 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274323 A s)). Qed.
Lemma lem3274325 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274326 {A : Type'} : (term252 A) = (term252 A).
Proof. exact (MK_COMB (@lem3274325 A) (@lem3274324 A)). Qed.
Lemma lem3274341 {A : Type'} (x : type684 A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem3274342 {A : Type'} (x : type684 A) : (term288 A x) = (term288 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274341 A x s)). Qed.
Lemma lem3274343 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274344 {A : Type'} (x : type684 A) : (term290 A x) = (term290 A x).
Proof. exact (MK_COMB (@lem3274343 A) (@lem3274342 A x)). Qed.
Lemma lem3274345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3274346 {A : Type'} (x : type684 A) : (term309 A x) = (term309 A x).
Proof. exact (MK_COMB (@lem3274345) (@lem3274344 A x)). Qed.
Lemma lem3274347 {A : Type'} (x : type684 A) : (term311 A x) = (term311 A x).
Proof. exact (MK_COMB (@lem3274346 A x) (@lem3274326 A)). Qed.
Lemma lem3274348 {A : Type'} (x : type684 A) (h1 : term311 A x) : term311 A x.
Proof. exact (EQ_MP (@lem3274347 A x) (@lem3274301 A x h1)). Qed.
Lemma lem3274385 {A : Type'} (t : type667 A) (s : A -> Prop) (x : A) : (term315 A t s x) = (term315 A t s x).
Proof. exact (eq_refl (term315 A t s x)). Qed.
Lemma lem3274386 {A : Type'} (t : type667 A) (s : A -> Prop) : (term316 A t s) = (term316 A t s).
Proof. exact (fun_ext (fun x : A => @lem3274385 A t s x)). Qed.
Lemma lem3274387 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3274388 {A : Type'} (t : type667 A) (s : A -> Prop) : (term188 A t s) = (term188 A t s).
Proof. exact (MK_COMB (@lem3274387 A) (@lem3274386 A t s)). Qed.
Lemma lem3274389 {A : Type'} (t : type667 A) : (term190 A t) = (term190 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274388 A t s)). Qed.
Lemma lem3274390 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274391 {A : Type'} (t : type667 A) : (term192 A t) = (term192 A t).
Proof. exact (MK_COMB (@lem3274390 A) (@lem3274389 A t)). Qed.
Lemma lem3274410 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A s x t) = (term37 A s x t).
Proof. exact (eq_refl (term37 A s x t)). Qed.
Lemma lem3274411 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term47 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3274410 A s x t)). Qed.
Lemma lem3274412 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274413 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (term48 A s x).
Proof. exact (MK_COMB (@lem3274412 A) (@lem3274411 A s x)). Qed.
Lemma lem3274420 {A : Type'} (x : A) (s : A -> Prop) : (term72 A x s) = (term72 A x s).
Proof. exact (eq_refl (term72 A x s)). Qed.
Lemma lem3274421 {A : Type'} (s : A -> Prop) (x : A) : (term74 A s x) = (term74 A s x).
Proof. exact (MK_COMB (@lem3274420 A x s) (@lem3274413 A s x)). Qed.
Lemma lem3274422 {A : Type'} (s : A -> Prop) : (term87 A s) = (term87 A s).
Proof. exact (fun_ext (fun x : A => @lem3274421 A s x)). Qed.
Lemma lem3274423 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3274424 {A : Type'} (s : A -> Prop) : (term98 A s) = (term98 A s).
Proof. exact (MK_COMB (@lem3274423 A) (@lem3274422 A s)). Qed.
Lemma lem3274425 {A : Type'} : (term111 A) = (term111 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274424 A s)). Qed.
Lemma lem3274426 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274427 {A : Type'} : (term122 A) = (term122 A).
Proof. exact (MK_COMB (@lem3274426 A) (@lem3274425 A)). Qed.
Lemma lem3274428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3274429 {A : Type'} : (term124 A) = (term124 A).
Proof. exact (MK_COMB (@lem3274428) (@lem3274427 A)). Qed.
Lemma lem3274430 {A : Type'} (t : type667 A) : (term209 A t) = (term209 A t).
Proof. exact (MK_COMB (@lem3274429 A) (@lem3274391 A t)). Qed.
Lemma lem3274431 {A : Type'} (t : type667 A) (h1 : term209 A t) : term209 A t.
Proof. exact (EQ_MP (@lem3274430 A t) (@lem3274302 A t h1)). Qed.
Lemma lem3274450 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A s x t) = (term37 A s x t).
Proof. exact (eq_refl (term37 A s x t)). Qed.
Lemma lem3274451 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term47 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3274450 A s x t)). Qed.
Lemma lem3274452 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274453 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (term48 A s x).
Proof. exact (MK_COMB (@lem3274452 A) (@lem3274451 A s x)). Qed.
Lemma lem3274454 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (fun_ext (fun x : A => @lem3274453 A s x)). Qed.
Lemma lem3274455 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3274456 {A : Type'} (s : A -> Prop) : (term57 A s) = (term57 A s).
Proof. exact (MK_COMB (@lem3274455 A) (@lem3274454 A s)). Qed.
Lemma lem3274465 {A : Type'} (s : A -> Prop) : (term58 A s) = (term58 A s).
Proof. exact (eq_refl (term58 A s)). Qed.
Lemma lem3274466 {A : Type'} (s : A -> Prop) : (term60 A s) = (term60 A s).
Proof. exact (MK_COMB (@lem3274465 A s) (@lem3274456 A s)). Qed.
Lemma lem3274467 {A : Type'} (s : A -> Prop) (h1 : term60 A s) : term60 A s.
Proof. exact (EQ_MP (@lem3274466 A s) (@lem3274303 A s h1)). Qed.
Lemma lem3274468 {A : Type'} (s : A -> Prop) (h1 : term60 A s) : term57 A s.
Proof. exact (proj2 (@lem3274467 A s h1)). Qed.
Lemma lem3274470 {A : Type'} (t : type667 A) (h1 : term209 A t) : term192 A t.
Proof. exact (proj2 (@lem3274431 A t h1)). Qed.
Lemma lem3274473 {A : Type'} (x : type684 A) (h1 : term311 A x) : term290 A x.
Proof. exact (proj1 (@lem3274348 A x h1)). Qed.
Lemma lem3274485 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A s x t) = (term37 A s x t).
Proof. exact (eq_refl (term37 A s x t)). Qed.
Lemma lem3274486 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term47 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3274485 A s x t)). Qed.
Lemma lem3274487 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274488 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (term48 A s x).
Proof. exact (MK_COMB (@lem3274487 A) (@lem3274486 A s x)). Qed.
Lemma lem3274489 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (fun_ext (fun x : A => @lem3274488 A s x)). Qed.
Lemma lem3274490 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3274492 {A : Type'} (s : A -> Prop) : (term57 A s) = (term57 A s).
Proof. exact (MK_COMB (@lem3274490 A) (@lem3274489 A s)). Qed.
Lemma lem3274493 {A : Type'} (s : A -> Prop) (h1 : term60 A s) : term57 A s.
Proof. exact (EQ_MP (@lem3274492 A s) (@lem3274468 A s h1)). Qed.
Lemma lem3274561 {A : Type'} (t : type667 A) (s : A -> Prop) (x : A) : (term315 A t s x) = (term317 A t s x).
Proof. exact (@lem19490 (s = (term318 A t s x)) (term39 A x s) (term319 A t s x)). Qed.
Lemma lem3274562 {A : Type'} (t : type667 A) (s : A -> Prop) : (term316 A t s) = (term320 A t s).
Proof. exact (fun_ext (fun x : A => @lem3274561 A t s x)). Qed.
Lemma lem3274563 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3274564 {A : Type'} (t : type667 A) (s : A -> Prop) : (term188 A t s) = (term321 A t s).
Proof. exact (MK_COMB (@lem3274563 A) (@lem3274562 A t s)). Qed.
Lemma lem3274565 {A : Type'} (t : type667 A) : (term190 A t) = (term322 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274564 A t s)). Qed.
Lemma lem3274566 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274568 {A : Type'} (t : type667 A) : (term192 A t) = (term323 A t).
Proof. exact (MK_COMB (@lem3274566 A) (@lem3274565 A t)). Qed.
Lemma lem3274569 {A : Type'} (t : type667 A) (h1 : term209 A t) : term323 A t.
Proof. exact (EQ_MP (@lem3274568 A t) (@lem3274470 A t h1)). Qed.
Lemma lem3274577 {A : Type'} (x : type684 A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem3274578 {A : Type'} (x : type684 A) : (term288 A x) = (term288 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3274577 A x s)). Qed.
Lemma lem3274579 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3274581 {A : Type'} (x : type684 A) : (term290 A x) = (term290 A x).
Proof. exact (MK_COMB (@lem3274579 A) (@lem3274578 A x)). Qed.
Lemma lem3274582 {A : Type'} (x : type684 A) (h1 : term311 A x) : term290 A x.
Proof. exact (EQ_MP (@lem3274581 A x) (@lem3274473 A x h1)). Qed.
Lemma lem3274625 {A : Type'} (_33456 : A) (s : A -> Prop) (h1 : term60 A s) : term324 A s _33456.
Proof. exact (@lem3274493 A s h1 _33456). Qed.
Lemma lem3274626 {A : Type'} (s : A -> Prop) (_33456 : A) : (term324 A s _33456) = (term48 A s _33456).
Proof. exact (eq_refl (term324 A s _33456)). Qed.
Lemma lem3274627 {A : Type'} (_33456 : A) (s : A -> Prop) (h1 : term60 A s) : term48 A s _33456.
Proof. exact (EQ_MP (@lem3274626 A s _33456) (@lem3274625 A _33456 s h1)). Qed.
Lemma lem3274628 {A : Type'} (_33456 : A) (_33457 : A -> Prop) (s : A -> Prop) (h1 : term60 A s) : term325 A s _33456 _33457.
Proof. exact (@lem3274627 A _33456 s h1 _33457). Qed.
Lemma lem3274629 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term325 A s _33456 _33457) = (term37 A s _33456 _33457).
Proof. exact (eq_refl (term325 A s _33456 _33457)). Qed.
Lemma lem3274640 {A : Type'} (_33461 : A -> Prop) (t : type667 A) (h1 : term209 A t) : term326 A t _33461.
Proof. exact (@lem3274569 A t h1 _33461). Qed.
Lemma lem3274641 {A : Type'} (t : type667 A) (_33461 : A -> Prop) : (term326 A t _33461) = (term321 A t _33461).
Proof. exact (eq_refl (term326 A t _33461)). Qed.
Lemma lem3274642 {A : Type'} (_33461 : A -> Prop) (t : type667 A) (h1 : term209 A t) : term321 A t _33461.
Proof. exact (EQ_MP (@lem3274641 A t _33461) (@lem3274640 A _33461 t h1)). Qed.
Lemma lem3274643 {A : Type'} (_33461 : A -> Prop) (_33462 : A) (t : type667 A) (h1 : term209 A t) : term327 A t _33461 _33462.
Proof. exact (@lem3274642 A _33461 t h1 _33462). Qed.
Lemma lem3274644 {A : Type'} (t : type667 A) (_33461 : A -> Prop) (_33462 : A) : (term327 A t _33461 _33462) = (term317 A t _33461 _33462).
Proof. exact (eq_refl (term327 A t _33461 _33462)). Qed.
Lemma lem3274645 {A : Type'} (_33461 : A -> Prop) (_33462 : A) (t : type667 A) (h1 : term209 A t) : term317 A t _33461 _33462.
Proof. exact (EQ_MP (@lem3274644 A t _33461 _33462) (@lem3274643 A _33461 _33462 t h1)). Qed.
Lemma lem3274646 {A : Type'} (_33463 : A -> Prop) (x : type684 A) (h1 : term311 A x) : term328 A x _33463.
Proof. exact (@lem3274582 A x h1 _33463). Qed.
Lemma lem3274647 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : (term328 A x _33463) = (term286 A x _33463).
Proof. exact (eq_refl (term328 A x _33463)). Qed.
Lemma lem3274658 {A : Type'} (s : A -> Prop) (h1 : term60 A s) : term17 A s.
Proof. exact (proj1 (@lem3274467 A s h1)). Qed.
Lemma lem3274664 {A : Type'} (_33456 : A) (_33457 : A -> Prop) (s : A -> Prop) (h1 : term60 A s) : term37 A s _33456 _33457.
Proof. exact (EQ_MP (@lem3274629 A s _33456 _33457) (@lem3274628 A _33456 _33457 s h1)). Qed.
Lemma lem3274680 {A : Type'} (_33463 : A -> Prop) (x : type684 A) (h1 : term311 A x) : term286 A x _33463.
Proof. exact (EQ_MP (@lem3274647 A x _33463) (@lem3274646 A _33463 x h1)). Qed.
Lemma lem3274692 {A : Type'} (_33461 : A -> Prop) (_33462 : A) (t : type667 A) (h1 : term209 A t) : term329 A t _33461 _33462.
Proof. exact (proj1 (@lem3274645 A _33461 _33462 t h1)). Qed.
Lemma lem3274698 {A : Type'} (_33461 : A -> Prop) (_33462 : A) (t : type667 A) (h1 : term209 A t) : term330 A t _33461 _33462.
Proof. exact (proj2 (@lem3274645 A _33461 _33462 t h1)). Qed.
Lemma lem3274762 {A : Type'} (s : A -> Prop) (h1 : term17 A s) : term17 A s.
Proof. exact (h1). Qed.
Lemma lem3274763 {A : Type'} (s : A -> Prop) (h1 : term17 A s) : term331 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem3274762 A s h1). Qed.
Lemma lem3274765 (p : Prop) : (term332 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3274766 {A : Type'} (s : A -> Prop) : (term331 A s) = (term17 A s).
Proof. exact (@lem3274765 (s = (@EMPTY A))). Qed.
Lemma lem3274767 {A : Type'} (s : A -> Prop) (h1 : term17 A s) : term17 A s.
Proof. exact (EQ_MP (@lem3274766 A s) (@lem3274763 A s h1)). Qed.
Lemma lem3274769 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3274772 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : (term286 A x _33463) = (term334 A x _33463).
Proof. exact (@lem3274769 (_33463 = (@EMPTY A)) (term335 A x _33463)). Qed.
Lemma lem3274775 {A : Type'} (_33463 : A -> Prop) (x : type684 A) (h1 : term311 A x) : term334 A x _33463.
Proof. exact (EQ_MP (@lem3274772 A x _33463) (@lem3274680 A _33463 x h1)). Qed.
Lemma lem3274776 {A : Type'} (_33463 : A -> Prop) (x : type684 A) (h1 : term311 A x) : term334 A x _33463.
Proof. exact (@lem3274775 A _33463 x h1). Qed.
Lemma lem3274777 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term311 A x) : term334 A x s.
Proof. exact (@lem3274776 A s x h1). Qed.
Lemma lem3274780 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term17 A s) (h2 : term311 A x) : term335 A x s.
Proof. exact (@lem3274777 A s x h2 (@lem3274767 A s h1)). Qed.
Lemma lem3274781 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term17 A s) (h2 : term311 A x) : term336 A x s.
Proof. exact (fun h0 : term337 A x s => @lem3274780 A s x h1 h2). Qed.
Lemma lem3274783 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3274784 {A : Type'} (x : type684 A) (s : A -> Prop) : (term336 A x s) = (term335 A x s).
Proof. exact (@lem3274783 (term335 A x s)). Qed.
Lemma lem3274785 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term17 A s) (h2 : term311 A x) : term335 A x s.
Proof. exact (EQ_MP (@lem3274784 A x s) (@lem3274781 A s x h1 h2)). Qed.
Lemma lem3274791 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3274792 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : (term329 A t _33461 _33462) = (term339 A t _33462 _33461).
Proof. exact (@lem3274791 (_33461 = (term318 A t _33461 _33462)) (term39 A _33462 _33461)). Qed.
Lemma lem3274800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3274801 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : (term340 A t _33461 _33462) = (term341 A t _33462 _33461).
Proof. exact (MK_COMB (@lem3274800) (@lem3274792 A t _33462 _33461)). Qed.
Lemma lem3274809 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : (term339 A t _33462 _33461) = (term339 A t _33462 _33461).
Proof. exact (eq_refl (term339 A t _33462 _33461)). Qed.
Lemma lem3274810 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : ((term329 A t _33461 _33462) = (term339 A t _33462 _33461)) = ((term339 A t _33462 _33461) = (term339 A t _33462 _33461)).
Proof. exact (MK_COMB (@lem3274801 A t _33462 _33461) (@lem3274809 A t _33462 _33461)). Qed.
Lemma lem3274812 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3274813 (x : Prop) : (x = x) = True.
Proof. exact (@lem3274812 Prop x). Qed.
Lemma lem3274814 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : ((term339 A t _33462 _33461) = (term339 A t _33462 _33461)) = True.
Proof. exact (@lem3274813 (term339 A t _33462 _33461)). Qed.
Lemma lem3274815 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : ((term329 A t _33461 _33462) = (term339 A t _33462 _33461)) = True.
Proof. exact (TRANS (@lem3274810 A t _33462 _33461) (@lem3274814 A t _33462 _33461)). Qed.
Lemma lem3274816 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : True = ((term329 A t _33461 _33462) = (term339 A t _33462 _33461)).
Proof. exact (SYM (@lem3274815 A t _33462 _33461)). Qed.
Lemma lem3274817 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : (term329 A t _33461 _33462) = (term339 A t _33462 _33461).
Proof. exact (EQ_MP (@lem3274816 A t _33462 _33461) (@lem0)). Qed.
Lemma lem3274818 {A : Type'} (_33462 : A) (_33461 : A -> Prop) (t : type667 A) (h1 : term209 A t) : term339 A t _33462 _33461.
Proof. exact (EQ_MP (@lem3274817 A t _33462 _33461) (@lem3274692 A _33461 _33462 t h1)). Qed.
Lemma lem3274820 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3274821 {A : Type'} (t : type667 A) (_33461 : A -> Prop) (_33462 : A) : (term339 A t _33462 _33461) = (term342 A t _33461 _33462).
Proof. exact (@lem3274820 (term39 A _33462 _33461) (_33461 = (term318 A t _33461 _33462))). Qed.
Lemma lem3274823 (a : Prop) : (term343 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3274824 {A : Type'} (_33462 : A) (_33461 : A -> Prop) : (term34 A _33462 _33461) = (@IN A _33462 _33461).
Proof. exact (@lem3274823 (@IN A _33462 _33461)). Qed.
Lemma lem3274825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3274826 {A : Type'} (_33462 : A) (_33461 : A -> Prop) : (term344 A _33462 _33461) = (term345 A _33462 _33461).
Proof. exact (MK_COMB (@lem3274825) (@lem3274824 A _33462 _33461)). Qed.
Lemma lem3274827 {A : Type'} (t : type667 A) (_33461 : A -> Prop) (_33462 : A) : (_33461 = (term318 A t _33461 _33462)) = (_33461 = (term318 A t _33461 _33462)).
Proof. exact (eq_refl (_33461 = (term318 A t _33461 _33462))). Qed.
Lemma lem3274828 {A : Type'} (t : type667 A) (_33461 : A -> Prop) (_33462 : A) : (term342 A t _33461 _33462) = (term346 A t _33461 _33462).
Proof. exact (MK_COMB (@lem3274826 A _33462 _33461) (@lem3274827 A t _33461 _33462)). Qed.
Lemma lem3274829 {A : Type'} (t : type667 A) (_33461 : A -> Prop) (_33462 : A) : (term339 A t _33462 _33461) = (term346 A t _33461 _33462).
Proof. exact (TRANS (@lem3274821 A t _33461 _33462) (@lem3274828 A t _33461 _33462)). Qed.
Lemma lem3274832 {A : Type'} (_33461 : A -> Prop) (_33462 : A) (t : type667 A) (h1 : term209 A t) : term346 A t _33461 _33462.
Proof. exact (EQ_MP (@lem3274829 A t _33461 _33462) (@lem3274818 A _33462 _33461 t h1)). Qed.
Lemma lem3274833 {A : Type'} (_33461 : A -> Prop) (_33462 : A) (t : type667 A) (h1 : term209 A t) : term346 A t _33461 _33462.
Proof. exact (@lem3274832 A _33461 _33462 t h1). Qed.
Lemma lem3274834 {A : Type'} (x : type684 A) (s : A -> Prop) (t : type667 A) (h1 : term209 A t) : term347 A t x s.
Proof. exact (@lem3274833 A s (x s) t h1). Qed.
Lemma lem3274837 {A : Type'} (s : A -> Prop) (t : type667 A) (x : type684 A) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) : s = (term348 A t x s).
Proof. exact (@lem3274834 A x s t h2 (@lem3274785 A s x h1 h3)). Qed.
Lemma lem3274838 {A : Type'} (s : A -> Prop) (t : type667 A) (x : type684 A) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) : term349 A t x s.
Proof. exact (fun h0 : term350 A t x s => @lem3274837 A s t x h1 h2 h3). Qed.
Lemma lem3274840 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3274841 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) : (term349 A t x s) = (s = (term348 A t x s)).
Proof. exact (@lem3274840 (s = (term348 A t x s))). Qed.
Lemma lem3274842 {A : Type'} (s : A -> Prop) (t : type667 A) (x : type684 A) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) : s = (term348 A t x s).
Proof. exact (EQ_MP (@lem3274841 A t x s) (@lem3274838 A s t x h1 h2 h3)). Qed.
Lemma lem3274848 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3274849 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term37 A s _33456 _33457) = (term351 A s _33456 _33457).
Proof. exact (@lem3274848 (@IN A _33456 _33457) (term352 A s _33456 _33457)). Qed.
Lemma lem3274857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3274858 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term353 A s _33456 _33457) = (term354 A s _33456 _33457).
Proof. exact (MK_COMB (@lem3274857) (@lem3274849 A s _33456 _33457)). Qed.
Lemma lem3274866 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term351 A s _33456 _33457) = (term351 A s _33456 _33457).
Proof. exact (eq_refl (term351 A s _33456 _33457)). Qed.
Lemma lem3274867 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : ((term37 A s _33456 _33457) = (term351 A s _33456 _33457)) = ((term351 A s _33456 _33457) = (term351 A s _33456 _33457)).
Proof. exact (MK_COMB (@lem3274858 A s _33456 _33457) (@lem3274866 A s _33456 _33457)). Qed.
Lemma lem3274869 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3274870 (x : Prop) : (x = x) = True.
Proof. exact (@lem3274869 Prop x). Qed.
Lemma lem3274871 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : ((term351 A s _33456 _33457) = (term351 A s _33456 _33457)) = True.
Proof. exact (@lem3274870 (term351 A s _33456 _33457)). Qed.
Lemma lem3274872 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : ((term37 A s _33456 _33457) = (term351 A s _33456 _33457)) = True.
Proof. exact (TRANS (@lem3274867 A s _33456 _33457) (@lem3274871 A s _33456 _33457)). Qed.
Lemma lem3274873 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : True = ((term37 A s _33456 _33457) = (term351 A s _33456 _33457)).
Proof. exact (SYM (@lem3274872 A s _33456 _33457)). Qed.
Lemma lem3274874 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term37 A s _33456 _33457) = (term351 A s _33456 _33457).
Proof. exact (EQ_MP (@lem3274873 A s _33456 _33457) (@lem0)). Qed.
Lemma lem3274875 {A : Type'} (_33456 : A) (_33457 : A -> Prop) (s : A -> Prop) (h1 : term60 A s) : term351 A s _33456 _33457.
Proof. exact (EQ_MP (@lem3274874 A s _33456 _33457) (@lem3274664 A _33456 _33457 s h1)). Qed.
Lemma lem3274877 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3274878 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term351 A s _33456 _33457) = (term355 A s _33456 _33457).
Proof. exact (@lem3274877 (term352 A s _33456 _33457) (@IN A _33456 _33457)). Qed.
Lemma lem3274880 (a : Prop) : (term343 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3274881 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term356 A s _33456 _33457) = (s = (@INSERT A _33456 _33457)).
Proof. exact (@lem3274880 (s = (@INSERT A _33456 _33457))). Qed.
Lemma lem3274882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3274883 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term357 A s _33456 _33457) = (term358 A s _33456 _33457).
Proof. exact (MK_COMB (@lem3274882) (@lem3274881 A s _33456 _33457)). Qed.
Lemma lem3274884 {A : Type'} (_33456 : A) (_33457 : A -> Prop) : (@IN A _33456 _33457) = (@IN A _33456 _33457).
Proof. exact (eq_refl (@IN A _33456 _33457)). Qed.
Lemma lem3274885 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term355 A s _33456 _33457) = (term359 A s _33456 _33457).
Proof. exact (MK_COMB (@lem3274883 A s _33456 _33457) (@lem3274884 A _33456 _33457)). Qed.
Lemma lem3274886 {A : Type'} (s : A -> Prop) (_33456 : A) (_33457 : A -> Prop) : (term351 A s _33456 _33457) = (term359 A s _33456 _33457).
Proof. exact (TRANS (@lem3274878 A s _33456 _33457) (@lem3274885 A s _33456 _33457)). Qed.
Lemma lem3274889 {A : Type'} (_33456 : A) (_33457 : A -> Prop) (s : A -> Prop) (h1 : term60 A s) : term359 A s _33456 _33457.
Proof. exact (EQ_MP (@lem3274886 A s _33456 _33457) (@lem3274875 A _33456 _33457 s h1)). Qed.
Lemma lem3274890 {A : Type'} (_33456 : A) (_33457 : A -> Prop) (s : A -> Prop) (h1 : term60 A s) : term359 A s _33456 _33457.
Proof. exact (@lem3274889 A _33456 _33457 s h1). Qed.
Lemma lem3274891 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term60 A s) : term360 A t x s.
Proof. exact (@lem3274890 A (x s) (term361 A t x s) s h1). Qed.
Lemma lem3274894 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) (h4 : term60 A s) : term362 A t x s.
Proof. exact (@lem3274891 A t x s h4 (@lem3274842 A s t x h1 h2 h3)). Qed.
Lemma lem3274895 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) (h4 : term60 A s) : term363 A t x s.
Proof. exact (fun h0 : term364 A t x s => @lem3274894 A t x s h1 h2 h3 h4). Qed.
Lemma lem3274897 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3274898 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) : (term363 A t x s) = (term362 A t x s).
Proof. exact (@lem3274897 (term362 A t x s)). Qed.
Lemma lem3274899 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) (h4 : term60 A s) : term362 A t x s.
Proof. exact (EQ_MP (@lem3274898 A t x s) (@lem3274895 A t x s h1 h2 h3 h4)). Qed.
Lemma lem3274901 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3274902 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : (term330 A t _33461 _33462) = (term365 A t _33462 _33461).
Proof. exact (@lem3274901 (term319 A t _33461 _33462) (term39 A _33462 _33461)). Qed.
Lemma lem3274904 (a : Prop) : (term343 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3274905 {A : Type'} (t : type667 A) (_33461 : A -> Prop) (_33462 : A) : (term366 A t _33461 _33462) = (term367 A t _33461 _33462).
Proof. exact (@lem3274904 (term367 A t _33461 _33462)). Qed.
Lemma lem3274906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3274907 {A : Type'} (t : type667 A) (_33461 : A -> Prop) (_33462 : A) : (term368 A t _33461 _33462) = (term369 A t _33461 _33462).
Proof. exact (MK_COMB (@lem3274906) (@lem3274905 A t _33461 _33462)). Qed.
Lemma lem3274908 {A : Type'} (_33462 : A) (_33461 : A -> Prop) : (term39 A _33462 _33461) = (term39 A _33462 _33461).
Proof. exact (eq_refl (term39 A _33462 _33461)). Qed.
Lemma lem3274909 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : (term365 A t _33462 _33461) = (term370 A t _33462 _33461).
Proof. exact (MK_COMB (@lem3274907 A t _33461 _33462) (@lem3274908 A _33462 _33461)). Qed.
Lemma lem3274910 {A : Type'} (t : type667 A) (_33462 : A) (_33461 : A -> Prop) : (term330 A t _33461 _33462) = (term370 A t _33462 _33461).
Proof. exact (TRANS (@lem3274902 A t _33462 _33461) (@lem3274909 A t _33462 _33461)). Qed.
Lemma lem3274913 {A : Type'} (_33462 : A) (_33461 : A -> Prop) (t : type667 A) (h1 : term209 A t) : term370 A t _33462 _33461.
Proof. exact (EQ_MP (@lem3274910 A t _33462 _33461) (@lem3274698 A _33461 _33462 t h1)). Qed.
Lemma lem3274914 {A : Type'} (_33462 : A) (_33461 : A -> Prop) (t : type667 A) (h1 : term209 A t) : term370 A t _33462 _33461.
Proof. exact (@lem3274913 A _33462 _33461 t h1). Qed.
Lemma lem3274915 {A : Type'} (x : type684 A) (s : A -> Prop) (t : type667 A) (h1 : term209 A t) : term371 A t x s.
Proof. exact (@lem3274914 A (x s) s t h1). Qed.
Lemma lem3274918 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) (h4 : term60 A s) : term337 A x s.
Proof. exact (@lem3274915 A x s t h2 (@lem3274899 A t x s h1 h2 h3 h4)). Qed.
Lemma lem3274919 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) (h4 : term60 A s) : term372 A x s.
Proof. exact (fun h0 : term335 A x s => @lem3274918 A t x s h1 h2 h3 h4). Qed.
Lemma lem3274921 (p : Prop) : (term332 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3274922 {A : Type'} (x : type684 A) (s : A -> Prop) : (term372 A x s) = (term337 A x s).
Proof. exact (@lem3274921 (term335 A x s)). Qed.
Lemma lem3274923 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) (h4 : term60 A s) : term337 A x s.
Proof. exact (EQ_MP (@lem3274922 A x s) (@lem3274919 A t x s h1 h2 h3 h4)). Qed.
Lemma lem3274929 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3274930 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : (term286 A x _33463) = (term373 A x _33463).
Proof. exact (@lem3274929 (_33463 = (@EMPTY A)) (term335 A x _33463)). Qed.
Lemma lem3274938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3274939 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : (term374 A x _33463) = (term375 A x _33463).
Proof. exact (MK_COMB (@lem3274938) (@lem3274930 A x _33463)). Qed.
Lemma lem3274947 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : (term373 A x _33463) = (term373 A x _33463).
Proof. exact (eq_refl (term373 A x _33463)). Qed.
Lemma lem3274948 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : ((term286 A x _33463) = (term373 A x _33463)) = ((term373 A x _33463) = (term373 A x _33463)).
Proof. exact (MK_COMB (@lem3274939 A x _33463) (@lem3274947 A x _33463)). Qed.
Lemma lem3274950 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3274951 (x : Prop) : (x = x) = True.
Proof. exact (@lem3274950 Prop x). Qed.
Lemma lem3274952 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : ((term373 A x _33463) = (term373 A x _33463)) = True.
Proof. exact (@lem3274951 (term373 A x _33463)). Qed.
Lemma lem3274953 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : ((term286 A x _33463) = (term373 A x _33463)) = True.
Proof. exact (TRANS (@lem3274948 A x _33463) (@lem3274952 A x _33463)). Qed.
Lemma lem3274954 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : True = ((term286 A x _33463) = (term373 A x _33463)).
Proof. exact (SYM (@lem3274953 A x _33463)). Qed.
Lemma lem3274955 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : (term286 A x _33463) = (term373 A x _33463).
Proof. exact (EQ_MP (@lem3274954 A x _33463) (@lem0)). Qed.
Lemma lem3274956 {A : Type'} (_33463 : A -> Prop) (x : type684 A) (h1 : term311 A x) : term373 A x _33463.
Proof. exact (EQ_MP (@lem3274955 A x _33463) (@lem3274680 A _33463 x h1)). Qed.
Lemma lem3274958 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3274961 {A : Type'} (x : type684 A) (_33463 : A -> Prop) : (term373 A x _33463) = (term376 A x _33463).
Proof. exact (@lem3274958 (term335 A x _33463) (_33463 = (@EMPTY A))). Qed.
Lemma lem3274964 {A : Type'} (_33463 : A -> Prop) (x : type684 A) (h1 : term311 A x) : term376 A x _33463.
Proof. exact (EQ_MP (@lem3274961 A x _33463) (@lem3274956 A _33463 x h1)). Qed.
Lemma lem3274965 {A : Type'} (_33463 : A -> Prop) (x : type684 A) (h1 : term311 A x) : term376 A x _33463.
Proof. exact (@lem3274964 A _33463 x h1). Qed.
Lemma lem3274966 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term311 A x) : term376 A x s.
Proof. exact (@lem3274965 A s x h1). Qed.
Lemma lem3274969 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term17 A s) (h2 : term209 A t) (h3 : term311 A x) (h4 : term60 A s) : s = (@EMPTY A).
Proof. exact (@lem3274966 A s x h3 (@lem3274923 A t x s h1 h2 h3 h4)). Qed.
Lemma lem3274970 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : term377 A s.
Proof. exact (fun h0 : term17 A s => @lem3274969 A t x s h0 h1 h2 h3). Qed.
Lemma lem3274972 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3274973 {A : Type'} (s : A -> Prop) : (term377 A s) = (s = (@EMPTY A)).
Proof. exact (@lem3274972 (s = (@EMPTY A))). Qed.
Lemma lem3274974 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : s = (@EMPTY A).
Proof. exact (EQ_MP (@lem3274973 A s) (@lem3274970 A t x s h1 h2 h3)). Qed.
Lemma lem3274977 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3274979 {A : Type'} (s : A -> Prop) : (term17 A s) = (term378 A s).
Proof. exact (@lem3274977 (s = (@EMPTY A))). Qed.
Lemma lem3274982 {A : Type'} (s : A -> Prop) (h1 : term60 A s) : term378 A s.
Proof. exact (EQ_MP (@lem3274979 A s) (@lem3274658 A s h1)). Qed.
Lemma lem3274985 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : False.
Proof. exact (@lem3274982 A s h3 (@lem3274974 A t x s h1 h2 h3)). Qed.
Lemma lem3274986 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : term379.
Proof. exact (fun h0 : ~ False => @lem3274985 A t x s h1 h2 h3). Qed.
Lemma lem3274988 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3274989 : term379 = False.
Proof. exact (@lem3274988 False). Qed.
Lemma lem3274990 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : False.
Proof. exact (EQ_MP (@lem3274989) (@lem3274986 A t x s h1 h2 h3)). Qed.
Lemma lem3274991 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : (term60 A s) = False.
Proof. exact (prop_ext (fun h4 : term60 A s => @lem3274990 A t x s h1 h2 h3) (fun h4 : False => @lem3274467 A s h3)). Qed.
Lemma lem3274992 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : False.
Proof. exact (EQ_MP (@lem3274991 A t x s h1 h2 h3) (@lem3274467 A s h3)). Qed.
Lemma lem3274993 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : (term209 A t) = False.
Proof. exact (prop_ext (fun h4 : term209 A t => @lem3274992 A t x s h1 h2 h3) (fun h4 : False => @lem3274431 A t h1)). Qed.
Lemma lem3274994 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : False.
Proof. exact (EQ_MP (@lem3274993 A t x s h1 h2 h3) (@lem3274431 A t h1)). Qed.
Lemma lem3274995 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : (term311 A x) = False.
Proof. exact (prop_ext (fun h4 : term311 A x => @lem3274994 A t x s h1 h2 h3) (fun h4 : False => @lem3274348 A x h2)). Qed.
Lemma lem3274996 {A : Type'} (t : type667 A) (x : type684 A) (s : A -> Prop) (h1 : term209 A t) (h2 : term311 A x) (h3 : term60 A s) : False.
Proof. exact (EQ_MP (@lem3274995 A t x s h1 h2 h3) (@lem3274348 A x h2)). Qed.
Lemma lem3274997 {A : Type'} (t : type667 A) (x : type684 A) (h1 : term3 A) (h2 : term209 A t) (h3 : term311 A x) : False.
Proof. exact (ex_elim (@lem3273432 A h1) (fun s : A -> Prop => fun h0 : term68 A s => @lem3274996 A t x s h2 h3 h0)). Qed.
Lemma lem3274998 {A : Type'} (x : type684 A) (h1 : term5 A) (h2 : term3 A) (h3 : term311 A x) : False.
Proof. exact (ex_elim (@lem3274046 A h1) (fun t : type667 A => fun h0 : term211 A t => @lem3274997 A t x h2 h0 h3)). Qed.
Lemma lem3274999 {A : Type'} (h1 : term5 A) (h2 : term4 A) (h3 : term3 A) : False.
Proof. exact (ex_elim (@lem3274300 A h2) (fun x : type684 A => fun h0 : term313 A x => @lem3274998 A x h1 h3 h0)). Qed.
Lemma lem3275000 {A : Type'} (h1 : term5 A) (h2 : term3 A) : term10 A.
Proof. exact (fun h0 : term4 A => @lem3274999 A h1 h0 h2). Qed.
Lemma lem3275001 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem3275002 {A : Type'} (h1 : term5 A) (h2 : term3 A) : term11 A.
Proof. exact (EQ_MP (@lem3275001 A) (@lem3275000 A h1 h2)). Qed.
Lemma lem3275003 {A : Type'} (h1 : term3 A) : term14 A.
Proof. exact (fun h0 : term5 A => @lem3275002 A h0 h1). Qed.
Lemma lem3275004 {A : Type'} : term16 A.
Proof. exact (fun h0 : term3 A => @lem3275003 A h0). Qed.
Lemma lem3275005 {A : Type'} : term6 A.
Proof. exact (EQ_MP (@lem3273279 A) (@lem3275004 A)). Qed.
Lemma lem3275007 {A : Type'} : term6 A.
Proof. exact (@lem3272965 A (@lem3275005 A)). Qed.
Lemma lem3275008 {A : Type'} (h1 : term3 A) : term13 A.
Proof. exact (@lem3275007 A (@lem3272943 A h1)). Qed.
Lemma lem3275009 {A : Type'} (h1 : term3 A) : term10 A.
Proof. exact (@lem3275008 A h1 (@lem3272947 A)). Qed.
Lemma lem3275010 {A : Type'} (h1 : term3 A) : False.
Proof. exact (@lem3275009 A h1 (@lem3272944 A)). Qed.
Lemma lem3275011 {A : Type'} (h1 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h2 : term3 A => @lem3275010 A h1) (fun h2 : False => @lem3272943 A h1)). Qed.
Lemma lem3275012 {A : Type'} (h1 : term3 A) : False.
Proof. exact (EQ_MP (@lem3275011 A h1) (@lem3272943 A h1)). Qed.
Lemma lem3275013 {A : Type'} : term2 A.
Proof. exact (fun h0 : term3 A => @lem3275012 A h0). Qed.
Lemma lem3275014 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem3272942 A) (@lem3275013 A)). Qed.
