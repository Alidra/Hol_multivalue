Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_TYBIT0_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_TYBIT0_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem7933985 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7933986 {A : Type'} : (@FINITE (tybit0 A) (@UNIV (tybit0 A))) = (term1 A).
Proof. exact (@lem7933985 (@FINITE (tybit0 A) (@UNIV (tybit0 A)))). Qed.
Lemma lem7933987 {A : Type'} : (term1 A) = (@FINITE (tybit0 A) (@UNIV (tybit0 A))).
Proof. exact (SYM (@lem7933986 A)). Qed.
Lemma lem7933988 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7933989 {A : Type'} : term3 A.
Proof. exact (@lem7932264 A). Qed.
Lemma lem7933990 {A : Type'} : term4 A.
Proof. exact (@lem7932264 (tybit0 A)). Qed.
Lemma lem7933991 {A : Type'} : term5 A.
Proof. exact (@lem3863773 (type1680 A)). Qed.
Lemma lem7933992 {A : Type'} : term6 A.
Proof. exact (@lem3863773 (tybit0 A)). Qed.
Lemma lem7933996 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7933997 {A : Type'} : term8 A.
Proof. exact (fun h0 : term7 A => @lem7933996 A h0). Qed.
Lemma lem7933998 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem7933999 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7934000 {A : Type'} (h1 : term7 A) (h2 : term8 A) : term7 A.
Proof. exact (@lem7933998 A h2 (@lem7933999 A h1)). Qed.
Lemma lem7934001 {A : Type'} (h1 : term7 A) : term9 A.
Proof. exact (fun h0 : term8 A => @lem7934000 A h1 h0). Qed.
Lemma lem7934002 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem7934003 {A : Type'} (h1 : term7 A) (h2 : term8 A) : term7 A.
Proof. exact (@lem7934001 A h1 (@lem7934002 A h2)). Qed.
Lemma lem7934004 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (fun h0 : term7 A => @lem7934003 A h0 h1). Qed.
Lemma lem7934005 {A : Type'} : term10 A.
Proof. exact (fun h0 : term8 A => @lem7934004 A h0). Qed.
Lemma lem7934008 {A : Type'} : term8 A.
Proof. exact (@lem7934005 A (@lem7933997 A)). Qed.
Lemma lem7934009 {A : Type'} : term8 A.
Proof. exact (@lem7934008 A). Qed.
Lemma lem7934039 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7934040 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (@lem7934039 (term4 A)). Qed.
Lemma lem7934041 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (eq_refl (term13 A)). Qed.
Lemma lem7934042 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem7934041 A) (@lem7934040 A)). Qed.
Lemma lem7934045 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (eq_refl (term16 A)). Qed.
Lemma lem7934046 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem7934045 A) (@lem7934042 A)). Qed.
Lemma lem7934049 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem7934050 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem7934049 A) (@lem7934046 A)). Qed.
Lemma lem7934053 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem7934060 {A : Type'} : (term7 A) = (term23 A).
Proof. exact (MK_COMB (@lem7934053 A) (@lem7934050 A)). Qed.
Lemma lem7934067 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (eq_refl (term15 A)). Qed.
Lemma lem7934076 {A : Type'} (s : type1340 A) (n : nat) : ((@HAS_SIZE (tybit0 (tybit0 A)) s n) = (term24 A s n)) = ((@HAS_SIZE (tybit0 (tybit0 A)) s n) = (term24 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (tybit0 (tybit0 A)) s n) = (term24 A s n))). Qed.
Lemma lem7934077 {A : Type'} (s : type1340 A) : (term25 A s) = (term25 A s).
Proof. exact (fun_ext (fun n : nat => @lem7934076 A s n)). Qed.
Lemma lem7934078 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7934079 {A : Type'} (s : type1340 A) : (term26 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem7934078) (@lem7934077 A s)). Qed.
Lemma lem7934080 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : type1340 A => @lem7934079 A s)). Qed.
Lemma lem7934081 {A : Type'} : (@all ((tybit0 (tybit0 A)) -> Prop)) = (@all ((tybit0 (tybit0 A)) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 (tybit0 A)) -> Prop))). Qed.
Lemma lem7934082 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem7934081 A) (@lem7934080 A)). Qed.
Lemma lem7934083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7934084 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem7934083) (@lem7934082 A)). Qed.
Lemma lem7934085 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem7934084 A) (@lem7934067 A)). Qed.
Lemma lem7934094 {A : Type'} (s : type1345 A) (n : nat) : ((@HAS_SIZE (tybit0 A) s n) = (term28 A s n)) = ((@HAS_SIZE (tybit0 A) s n) = (term28 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (tybit0 A) s n) = (term28 A s n))). Qed.
Lemma lem7934095 {A : Type'} (s : type1345 A) : (term29 A s) = (term29 A s).
Proof. exact (fun_ext (fun n : nat => @lem7934094 A s n)). Qed.
Lemma lem7934096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7934097 {A : Type'} (s : type1345 A) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem7934096) (@lem7934095 A s)). Qed.
Lemma lem7934098 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (fun_ext (fun s : type1345 A => @lem7934097 A s)). Qed.
Lemma lem7934099 {A : Type'} : (@all ((tybit0 A) -> Prop)) = (@all ((tybit0 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 A) -> Prop))). Qed.
Lemma lem7934100 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem7934099 A) (@lem7934098 A)). Qed.
Lemma lem7934101 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7934102 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7934101) (@lem7934100 A)). Qed.
Lemma lem7934103 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem7934102 A) (@lem7934085 A)). Qed.
Lemma lem7934108 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem7934109 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem7934108 A) (@lem7934103 A)). Qed.
Lemma lem7934148 {A : Type'} : (term7 A) = (term23 A).
Proof. exact (TRANS (@lem7934060 A) (@lem7934109 A)). Qed.
Lemma lem7934149 {A : Type'} : (term23 A) = (term7 A).
Proof. exact (SYM (@lem7934148 A)). Qed.
Lemma lem7934151 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem7934160 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7934171 {A : Type'} (s : type1345 A) (n : nat) : (term32 A s n) = (term33 A s n).
Proof. exact (@lem17045 (@FINITE (tybit0 A) s) ((@CARD (tybit0 A) s) = n)). Qed.
Lemma lem7934177 {A : Type'} (s : type1345 A) (n : nat) : (term34 A s n) = (term34 A s n).
Proof. exact (eq_refl (term34 A s n)). Qed.
Lemma lem7934179 {A : Type'} (s : type1345 A) (n : nat) : (term35 A s n) = (term35 A s n).
Proof. exact (eq_refl (term35 A s n)). Qed.
Lemma lem7934180 {A : Type'} (s : type1345 A) (n : nat) : (term36 A s n) = (term37 A s n).
Proof. exact (MK_COMB (@lem7934179 A s n) (@lem7934171 A s n)). Qed.
Lemma lem7934181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7934182 {A : Type'} (s : type1345 A) (n : nat) : (term38 A s n) = (term39 A s n).
Proof. exact (MK_COMB (@lem7934181) (@lem7934180 A s n)). Qed.
Lemma lem7934183 {A : Type'} (s : type1345 A) (n : nat) : (term40 A s n) = (term41 A s n).
Proof. exact (MK_COMB (@lem7934182 A s n) (@lem7934177 A s n)). Qed.
Lemma lem7934184 {A : Type'} (s : type1345 A) (n : nat) : ((@HAS_SIZE (tybit0 A) s n) = (term28 A s n)) = (term40 A s n).
Proof. exact (@lem17784 (@HAS_SIZE (tybit0 A) s n) (term28 A s n)). Qed.
Lemma lem7934185 {A : Type'} (s : type1345 A) (n : nat) : ((@HAS_SIZE (tybit0 A) s n) = (term28 A s n)) = (term41 A s n).
Proof. exact (TRANS (@lem7934184 A s n) (@lem7934183 A s n)). Qed.
Lemma lem7934186 {A : Type'} (s : type1345 A) : (term29 A s) = (term42 A s).
Proof. exact (fun_ext (fun n : nat => @lem7934185 A s n)). Qed.
Lemma lem7934187 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7934188 {A : Type'} (s : type1345 A) : (term30 A s) = (term43 A s).
Proof. exact (MK_COMB (@lem7934187) (@lem7934186 A s)). Qed.
Lemma lem7934189 {A : Type'} : (term31 A) = (term44 A).
Proof. exact (fun_ext (fun s : type1345 A => @lem7934188 A s)). Qed.
Lemma lem7934190 {A : Type'} : (@all ((tybit0 A) -> Prop)) = (@all ((tybit0 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 A) -> Prop))). Qed.
Lemma lem7934191 {A : Type'} : (term6 A) = (term45 A).
Proof. exact (MK_COMB (@lem7934190 A) (@lem7934189 A)). Qed.
Lemma lem7934197 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term46 A P Q) = (term47 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7934198 (P : nat -> Prop) (Q : nat -> Prop) : (term48 P Q) = (term49 P Q).
Proof. exact (@lem7934197 nat P Q). Qed.
Lemma lem7934199 {A : Type'} (s : type1345 A) : (term50 A s) = (term51 A s).
Proof. exact (@lem7934198 (term52 A s) (term53 A s)). Qed.
Lemma lem7934200 {A : Type'} (s : type1345 A) (n : nat) : (term54 A s n) = (term37 A s n).
Proof. exact (eq_refl (term54 A s n)). Qed.
Lemma lem7934201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7934202 {A : Type'} (s : type1345 A) (n : nat) : (term55 A s n) = (term39 A s n).
Proof. exact (MK_COMB (@lem7934201) (@lem7934200 A s n)). Qed.
Lemma lem7934203 {A : Type'} (s : type1345 A) (n : nat) : (term56 A s n) = (term34 A s n).
Proof. exact (eq_refl (term56 A s n)). Qed.
Lemma lem7934204 {A : Type'} (s : type1345 A) (n : nat) : (term57 A s n) = (term41 A s n).
Proof. exact (MK_COMB (@lem7934202 A s n) (@lem7934203 A s n)). Qed.
Lemma lem7934205 {A : Type'} (s : type1345 A) : (term58 A s) = (term42 A s).
Proof. exact (fun_ext (fun n : nat => @lem7934204 A s n)). Qed.
Lemma lem7934206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7934207 {A : Type'} (s : type1345 A) : (term50 A s) = (term43 A s).
Proof. exact (MK_COMB (@lem7934206) (@lem7934205 A s)). Qed.
Lemma lem7934208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7934209 {A : Type'} (s : type1345 A) : (term59 A s) = (term60 A s).
Proof. exact (MK_COMB (@lem7934208) (@lem7934207 A s)). Qed.
Lemma lem7934210 {A : Type'} (s : type1345 A) (n : nat) : (term54 A s n) = (term37 A s n).
Proof. exact (eq_refl (term54 A s n)). Qed.
Lemma lem7934211 {A : Type'} (s : type1345 A) : (term61 A s) = (term52 A s).
Proof. exact (fun_ext (fun n : nat => @lem7934210 A s n)). Qed.
Lemma lem7934212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7934213 {A : Type'} (s : type1345 A) : (term62 A s) = (term63 A s).
Proof. exact (MK_COMB (@lem7934212) (@lem7934211 A s)). Qed.
Lemma lem7934214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7934215 {A : Type'} (s : type1345 A) : (term64 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem7934214) (@lem7934213 A s)). Qed.
Lemma lem7934216 {A : Type'} (s : type1345 A) (n : nat) : (term56 A s n) = (term34 A s n).
Proof. exact (eq_refl (term56 A s n)). Qed.
Lemma lem7934217 {A : Type'} (s : type1345 A) : (term66 A s) = (term53 A s).
Proof. exact (fun_ext (fun n : nat => @lem7934216 A s n)). Qed.
Lemma lem7934218 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7934219 {A : Type'} (s : type1345 A) : (term67 A s) = (term68 A s).
Proof. exact (MK_COMB (@lem7934218) (@lem7934217 A s)). Qed.
Lemma lem7934220 {A : Type'} (s : type1345 A) : (term51 A s) = (term69 A s).
Proof. exact (MK_COMB (@lem7934215 A s) (@lem7934219 A s)). Qed.
Lemma lem7934221 {A : Type'} (s : type1345 A) : ((term50 A s) = (term51 A s)) = ((term43 A s) = (term69 A s)).
Proof. exact (MK_COMB (@lem7934209 A s) (@lem7934220 A s)). Qed.
Lemma lem7934222 {A : Type'} (s : type1345 A) : (term43 A s) = (term69 A s).
Proof. exact (EQ_MP (@lem7934221 A s) (@lem7934199 A s)). Qed.
Lemma lem7934319 {A : Type'} : (term44 A) = (term70 A).
Proof. exact (fun_ext (fun s : type1345 A => @lem7934222 A s)). Qed.
Lemma lem7934320 {A : Type'} : (@all ((tybit0 A) -> Prop)) = (@all ((tybit0 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 A) -> Prop))). Qed.
Lemma lem7934321 {A : Type'} : (term45 A) = (term71 A).
Proof. exact (MK_COMB (@lem7934320 A) (@lem7934319 A)). Qed.
Lemma lem7934323 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term46 A P Q) = (term47 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7934324 {A : Type'} (P : type385 A) (Q : type385 A) : (term72 A P Q) = (term73 A P Q).
Proof. exact (@lem7934323 (type1345 A) P Q). Qed.
Lemma lem7934325 {A : Type'} : (term74 A) = (term75 A).
Proof. exact (@lem7934324 A (term76 A) (term77 A)). Qed.
Lemma lem7934326 {A : Type'} (s : type1345 A) : (term78 A s) = (term63 A s).
Proof. exact (eq_refl (term78 A s)). Qed.
Lemma lem7934327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7934328 {A : Type'} (s : type1345 A) : (term79 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem7934327) (@lem7934326 A s)). Qed.
Lemma lem7934329 {A : Type'} (s : type1345 A) : (term80 A s) = (term68 A s).
Proof. exact (eq_refl (term80 A s)). Qed.
Lemma lem7934330 {A : Type'} (s : type1345 A) : (term81 A s) = (term69 A s).
Proof. exact (MK_COMB (@lem7934328 A s) (@lem7934329 A s)). Qed.
Lemma lem7934331 {A : Type'} : (term82 A) = (term70 A).
Proof. exact (fun_ext (fun s : type1345 A => @lem7934330 A s)). Qed.
Lemma lem7934332 {A : Type'} : (@all ((tybit0 A) -> Prop)) = (@all ((tybit0 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 A) -> Prop))). Qed.
Lemma lem7934333 {A : Type'} : (term74 A) = (term71 A).
Proof. exact (MK_COMB (@lem7934332 A) (@lem7934331 A)). Qed.
Lemma lem7934334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7934335 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (MK_COMB (@lem7934334) (@lem7934333 A)). Qed.
Lemma lem7934336 {A : Type'} (s : type1345 A) : (term78 A s) = (term63 A s).
Proof. exact (eq_refl (term78 A s)). Qed.
Lemma lem7934337 {A : Type'} : (term85 A) = (term76 A).
Proof. exact (fun_ext (fun s : type1345 A => @lem7934336 A s)). Qed.
Lemma lem7934338 {A : Type'} : (@all ((tybit0 A) -> Prop)) = (@all ((tybit0 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 A) -> Prop))). Qed.
Lemma lem7934339 {A : Type'} : (term86 A) = (term87 A).
Proof. exact (MK_COMB (@lem7934338 A) (@lem7934337 A)). Qed.
Lemma lem7934340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7934341 {A : Type'} : (term88 A) = (term89 A).
Proof. exact (MK_COMB (@lem7934340) (@lem7934339 A)). Qed.
Lemma lem7934342 {A : Type'} (s : type1345 A) : (term80 A s) = (term68 A s).
Proof. exact (eq_refl (term80 A s)). Qed.
Lemma lem7934343 {A : Type'} : (term90 A) = (term77 A).
Proof. exact (fun_ext (fun s : type1345 A => @lem7934342 A s)). Qed.
Lemma lem7934344 {A : Type'} : (@all ((tybit0 A) -> Prop)) = (@all ((tybit0 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 A) -> Prop))). Qed.
Lemma lem7934345 {A : Type'} : (term91 A) = (term92 A).
Proof. exact (MK_COMB (@lem7934344 A) (@lem7934343 A)). Qed.
Lemma lem7934346 {A : Type'} : (term75 A) = (term93 A).
Proof. exact (MK_COMB (@lem7934341 A) (@lem7934345 A)). Qed.
Lemma lem7934347 {A : Type'} : ((term74 A) = (term75 A)) = ((term71 A) = (term93 A)).
Proof. exact (MK_COMB (@lem7934335 A) (@lem7934346 A)). Qed.
Lemma lem7934348 {A : Type'} : (term71 A) = (term93 A).
Proof. exact (EQ_MP (@lem7934347 A) (@lem7934325 A)). Qed.
Lemma lem7934455 {A : Type'} : (term45 A) = (term93 A).
Proof. exact (TRANS (@lem7934321 A) (@lem7934348 A)). Qed.
Lemma lem7934456 {A : Type'} : (term6 A) = (term93 A).
Proof. exact (TRANS (@lem7934191 A) (@lem7934455 A)). Qed.
Lemma lem7934457 {A : Type'} (h1 : term6 A) : term93 A.
Proof. exact (EQ_MP (@lem7934456 A) (@lem7934151 A h1)). Qed.
Lemma lem7934760 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7934772 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7934795 {A : Type'} (s : type1345 A) (n : nat) : (term34 A s n) = (term34 A s n).
Proof. exact (eq_refl (term34 A s n)). Qed.
Lemma lem7934796 {A : Type'} (s : type1345 A) : (term53 A s) = (term53 A s).
Proof. exact (fun_ext (fun n : nat => @lem7934795 A s n)). Qed.
Lemma lem7934797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7934798 {A : Type'} (s : type1345 A) : (term68 A s) = (term68 A s).
Proof. exact (MK_COMB (@lem7934797) (@lem7934796 A s)). Qed.
Lemma lem7934799 {A : Type'} : (term77 A) = (term77 A).
Proof. exact (fun_ext (fun s : type1345 A => @lem7934798 A s)). Qed.
Lemma lem7934800 {A : Type'} : (@all ((tybit0 A) -> Prop)) = (@all ((tybit0 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 A) -> Prop))). Qed.
Lemma lem7934801 {A : Type'} : (term92 A) = (term92 A).
Proof. exact (MK_COMB (@lem7934800 A) (@lem7934799 A)). Qed.
Lemma lem7934826 {A : Type'} (s : type1345 A) (n : nat) : (term37 A s n) = (term37 A s n).
Proof. exact (eq_refl (term37 A s n)). Qed.
Lemma lem7934827 {A : Type'} (s : type1345 A) : (term52 A s) = (term52 A s).
Proof. exact (fun_ext (fun n : nat => @lem7934826 A s n)). Qed.
Lemma lem7934828 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7934829 {A : Type'} (s : type1345 A) : (term63 A s) = (term63 A s).
Proof. exact (MK_COMB (@lem7934828) (@lem7934827 A s)). Qed.
Lemma lem7934830 {A : Type'} : (term76 A) = (term76 A).
Proof. exact (fun_ext (fun s : type1345 A => @lem7934829 A s)). Qed.
Lemma lem7934831 {A : Type'} : (@all ((tybit0 A) -> Prop)) = (@all ((tybit0 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 A) -> Prop))). Qed.
Lemma lem7934832 {A : Type'} : (term87 A) = (term87 A).
Proof. exact (MK_COMB (@lem7934831 A) (@lem7934830 A)). Qed.
Lemma lem7934833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7934834 {A : Type'} : (term89 A) = (term89 A).
Proof. exact (MK_COMB (@lem7934833) (@lem7934832 A)). Qed.
Lemma lem7934835 {A : Type'} : (term93 A) = (term93 A).
Proof. exact (MK_COMB (@lem7934834 A) (@lem7934801 A)). Qed.
Lemma lem7934836 {A : Type'} (h1 : term6 A) : term93 A.
Proof. exact (EQ_MP (@lem7934835 A) (@lem7934457 A h1)). Qed.
Lemma lem7934918 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7934939 {A : Type'} (h1 : term6 A) : term92 A.
Proof. exact (proj2 (@lem7934836 A h1)). Qed.
Lemma lem7934944 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7934948 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7935040 {A : Type'} (s : type1345 A) (n : nat) : (term34 A s n) = (term94 A s n).
Proof. exact (@lem19490 (@FINITE (tybit0 A) s) (term95 A s n) ((@CARD (tybit0 A) s) = n)). Qed.
Lemma lem7935041 {A : Type'} (s : type1345 A) : (term53 A s) = (term96 A s).
Proof. exact (fun_ext (fun n : nat => @lem7935040 A s n)). Qed.
Lemma lem7935042 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7935043 {A : Type'} (s : type1345 A) : (term68 A s) = (term97 A s).
Proof. exact (MK_COMB (@lem7935042) (@lem7935041 A s)). Qed.
Lemma lem7935044 {A : Type'} : (term77 A) = (term98 A).
Proof. exact (fun_ext (fun s : type1345 A => @lem7935043 A s)). Qed.
Lemma lem7935045 {A : Type'} : (@all ((tybit0 A) -> Prop)) = (@all ((tybit0 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit0 A) -> Prop))). Qed.
Lemma lem7935047 {A : Type'} : (term92 A) = (term99 A).
Proof. exact (MK_COMB (@lem7935045 A) (@lem7935044 A)). Qed.
Lemma lem7935048 {A : Type'} (h1 : term6 A) : term99 A.
Proof. exact (EQ_MP (@lem7935047 A) (@lem7934939 A h1)). Qed.
Lemma lem7935067 {A : Type'} (_103859 : type1345 A) (h1 : term6 A) : term100 A _103859.
Proof. exact (@lem7935048 A h1 _103859). Qed.
Lemma lem7935068 {A : Type'} (_103859 : type1345 A) : (term100 A _103859) = (term97 A _103859).
Proof. exact (eq_refl (term100 A _103859)). Qed.
Lemma lem7935069 {A : Type'} (_103859 : type1345 A) (h1 : term6 A) : term97 A _103859.
Proof. exact (EQ_MP (@lem7935068 A _103859) (@lem7935067 A _103859 h1)). Qed.
Lemma lem7935070 {A : Type'} (_103859 : type1345 A) (_103860 : nat) (h1 : term6 A) : term101 A _103859 _103860.
Proof. exact (@lem7935069 A _103859 h1 _103860). Qed.
Lemma lem7935071 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : (term101 A _103859 _103860) = (term94 A _103859 _103860).
Proof. exact (eq_refl (term101 A _103859 _103860)). Qed.
Lemma lem7935072 {A : Type'} (_103859 : type1345 A) (_103860 : nat) (h1 : term6 A) : term94 A _103859 _103860.
Proof. exact (EQ_MP (@lem7935071 A _103859 _103860) (@lem7935070 A _103859 _103860 h1)). Qed.
Lemma lem7935078 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7935080 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7935108 {A : Type'} (_103860 : nat) (_103859 : type1345 A) (h1 : term6 A) : term102 A _103860 _103859.
Proof. exact (proj1 (@lem7935072 A _103859 _103860 h1)). Qed.
Lemma lem7935269 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7935270 {A : Type'} (h1 : term3 A) : term103 A.
Proof. exact (fun h0 : term104 A => @lem7935269 A h1). Qed.
Lemma lem7935272 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7935273 {A : Type'} : (term103 A) = (term3 A).
Proof. exact (@lem7935272 (term3 A)). Qed.
Lemma lem7935274 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (EQ_MP (@lem7935273 A) (@lem7935270 A h1)). Qed.
Lemma lem7935280 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7935281 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : (term102 A _103860 _103859) = (term106 A _103859 _103860).
Proof. exact (@lem7935280 (@FINITE (tybit0 A) _103859) (term95 A _103859 _103860)). Qed.
Lemma lem7935287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7935288 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : (term107 A _103860 _103859) = (term108 A _103859 _103860).
Proof. exact (MK_COMB (@lem7935287) (@lem7935281 A _103859 _103860)). Qed.
Lemma lem7935294 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : (term106 A _103859 _103860) = (term106 A _103859 _103860).
Proof. exact (eq_refl (term106 A _103859 _103860)). Qed.
Lemma lem7935295 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : ((term102 A _103860 _103859) = (term106 A _103859 _103860)) = ((term106 A _103859 _103860) = (term106 A _103859 _103860)).
Proof. exact (MK_COMB (@lem7935288 A _103859 _103860) (@lem7935294 A _103859 _103860)). Qed.
Lemma lem7935297 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7935298 (x : Prop) : (x = x) = True.
Proof. exact (@lem7935297 Prop x). Qed.
Lemma lem7935299 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : ((term106 A _103859 _103860) = (term106 A _103859 _103860)) = True.
Proof. exact (@lem7935298 (term106 A _103859 _103860)). Qed.
Lemma lem7935300 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : ((term102 A _103860 _103859) = (term106 A _103859 _103860)) = True.
Proof. exact (TRANS (@lem7935295 A _103859 _103860) (@lem7935299 A _103859 _103860)). Qed.
Lemma lem7935301 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : True = ((term102 A _103860 _103859) = (term106 A _103859 _103860)).
Proof. exact (SYM (@lem7935300 A _103859 _103860)). Qed.
Lemma lem7935302 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : (term102 A _103860 _103859) = (term106 A _103859 _103860).
Proof. exact (EQ_MP (@lem7935301 A _103859 _103860) (@lem0)). Qed.
Lemma lem7935303 {A : Type'} (_103859 : type1345 A) (_103860 : nat) (h1 : term6 A) : term106 A _103859 _103860.
Proof. exact (EQ_MP (@lem7935302 A _103859 _103860) (@lem7935108 A _103860 _103859 h1)). Qed.
Lemma lem7935305 (b : Prop) (a : Prop) : (a \/ b) = (term109 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7935306 {A : Type'} (_103860 : nat) (_103859 : type1345 A) : (term106 A _103859 _103860) = (term110 A _103860 _103859).
Proof. exact (@lem7935305 (term95 A _103859 _103860) (@FINITE (tybit0 A) _103859)). Qed.
Lemma lem7935308 (a : Prop) : (term111 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7935309 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : (term112 A _103859 _103860) = (@HAS_SIZE (tybit0 A) _103859 _103860).
Proof. exact (@lem7935308 (@HAS_SIZE (tybit0 A) _103859 _103860)). Qed.
Lemma lem7935310 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7935311 {A : Type'} (_103859 : type1345 A) (_103860 : nat) : (term113 A _103859 _103860) = (term114 A _103859 _103860).
Proof. exact (MK_COMB (@lem7935310) (@lem7935309 A _103859 _103860)). Qed.
Lemma lem7935312 {A : Type'} (_103859 : type1345 A) : (@FINITE (tybit0 A) _103859) = (@FINITE (tybit0 A) _103859).
Proof. exact (eq_refl (@FINITE (tybit0 A) _103859)). Qed.
Lemma lem7935313 {A : Type'} (_103860 : nat) (_103859 : type1345 A) : (term110 A _103860 _103859) = (term115 A _103860 _103859).
Proof. exact (MK_COMB (@lem7935311 A _103859 _103860) (@lem7935312 A _103859)). Qed.
Lemma lem7935314 {A : Type'} (_103860 : nat) (_103859 : type1345 A) : (term106 A _103859 _103860) = (term115 A _103860 _103859).
Proof. exact (TRANS (@lem7935306 A _103860 _103859) (@lem7935313 A _103860 _103859)). Qed.
Lemma lem7935317 {A : Type'} (_103860 : nat) (_103859 : type1345 A) (h1 : term6 A) : term115 A _103860 _103859.
Proof. exact (EQ_MP (@lem7935314 A _103860 _103859) (@lem7935303 A _103859 _103860 h1)). Qed.
Lemma lem7935318 {A : Type'} (_103860 : nat) (_103859 : type1345 A) (h1 : term6 A) : term115 A _103860 _103859.
Proof. exact (@lem7935317 A _103860 _103859 h1). Qed.
Lemma lem7935319 {A : Type'} (h1 : term6 A) : term116 A.
Proof. exact (@lem7935318 A (term117 A) (@UNIV (tybit0 A)) h1). Qed.
Lemma lem7935322 {A : Type'} (h1 : term6 A) (h2 : term3 A) : @FINITE (tybit0 A) (@UNIV (tybit0 A)).
Proof. exact (@lem7935319 A h1 (@lem7935274 A h2)). Qed.
Lemma lem7935323 {A : Type'} (h1 : term6 A) (h2 : term3 A) : term118 A.
Proof. exact (fun h0 : term2 A => @lem7935322 A h1 h2). Qed.
Lemma lem7935325 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7935326 {A : Type'} : (term118 A) = (@FINITE (tybit0 A) (@UNIV (tybit0 A))).
Proof. exact (@lem7935325 (@FINITE (tybit0 A) (@UNIV (tybit0 A)))). Qed.
Lemma lem7935327 {A : Type'} (h1 : term6 A) (h2 : term3 A) : @FINITE (tybit0 A) (@UNIV (tybit0 A)).
Proof. exact (EQ_MP (@lem7935326 A) (@lem7935323 A h1 h2)). Qed.
Lemma lem7935330 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7935332 {A : Type'} : (term2 A) = (term119 A).
Proof. exact (@lem7935330 (@FINITE (tybit0 A) (@UNIV (tybit0 A)))). Qed.
Lemma lem7935335 {A : Type'} (h1 : term2 A) : term119 A.
Proof. exact (EQ_MP (@lem7935332 A) (@lem7935078 A h1)). Qed.
Lemma lem7935338 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (@lem7935335 A h2 (@lem7935327 A h1 h3)). Qed.
Lemma lem7935339 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : term120.
Proof. exact (fun h0 : ~ False => @lem7935338 A h1 h2 h3). Qed.
Lemma lem7935341 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7935342 : term120 = False.
Proof. exact (@lem7935341 False). Qed.
Lemma lem7935343 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935342) (@lem7935339 A h1 h2 h3)). Qed.
Lemma lem7935344 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7935343 A h1 h2 h3) (fun h4 : False => @lem7935080 A h3)). Qed.
Lemma lem7935345 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935344 A h1 h2 h3) (@lem7935080 A h3)). Qed.
Lemma lem7935346 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7935345 A h1 h2 h3) (fun h4 : False => @lem7935078 A h2)). Qed.
Lemma lem7935347 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935346 A h1 h2 h3) (@lem7935078 A h2)). Qed.
Lemma lem7935348 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7935347 A h1 h2 h3) (fun h4 : False => @lem7934948 A h3)). Qed.
Lemma lem7935349 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935348 A h1 h2 h3) (@lem7934948 A h3)). Qed.
Lemma lem7935350 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7935349 A h1 h2 h3) (fun h4 : False => @lem7934944 A h2)). Qed.
Lemma lem7935351 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935350 A h1 h2 h3) (@lem7934944 A h2)). Qed.
Lemma lem7935352 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7935351 A h1 h2 h3) (fun h4 : False => @lem7934948 A h3)). Qed.
Lemma lem7935353 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935352 A h1 h2 h3) (@lem7934948 A h3)). Qed.
Lemma lem7935354 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7935353 A h1 h2 h3) (fun h4 : False => @lem7934944 A h2)). Qed.
Lemma lem7935355 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935354 A h1 h2 h3) (@lem7934944 A h2)). Qed.
Lemma lem7935356 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7935355 A h1 h2 h3) (fun h4 : False => @lem7934918 A h3)). Qed.
Lemma lem7935357 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935356 A h1 h2 h3) (@lem7934918 A h3)). Qed.
Lemma lem7935358 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7935357 A h1 h2 h3) (fun h4 : False => @lem7934772 A h2)). Qed.
Lemma lem7935359 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935358 A h1 h2 h3) (@lem7934772 A h2)). Qed.
Lemma lem7935360 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7935359 A h1 h2 h3) (fun h4 : False => @lem7934760 A h3)). Qed.
Lemma lem7935361 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935360 A h1 h2 h3) (@lem7934760 A h3)). Qed.
Lemma lem7935362 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7935361 A h1 h2 h3) (fun h4 : False => @lem7934160 A h2)). Qed.
Lemma lem7935363 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7935362 A h1 h2 h3) (@lem7934160 A h2)). Qed.
Lemma lem7935364 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : term11 A.
Proof. exact (fun h0 : term4 A => @lem7935363 A h1 h2 h3). Qed.
Lemma lem7935365 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem7935366 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : term12 A.
Proof. exact (EQ_MP (@lem7935365 A) (@lem7935364 A h1 h2 h3)). Qed.
Lemma lem7935367 {A : Type'} (h1 : term6 A) (h2 : term2 A) : term15 A.
Proof. exact (fun h0 : term3 A => @lem7935366 A h1 h2 h0). Qed.
Lemma lem7935368 {A : Type'} (h1 : term6 A) (h2 : term2 A) : term18 A.
Proof. exact (fun h0 : term5 A => @lem7935367 A h1 h2). Qed.
Lemma lem7935369 {A : Type'} (h1 : term2 A) : term21 A.
Proof. exact (fun h0 : term6 A => @lem7935368 A h0 h1). Qed.
Lemma lem7935370 {A : Type'} : term23 A.
Proof. exact (fun h0 : term2 A => @lem7935369 A h0). Qed.
Lemma lem7935371 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem7934149 A) (@lem7935370 A)). Qed.
Lemma lem7935373 {A : Type'} : term7 A.
Proof. exact (@lem7934009 A (@lem7935371 A)). Qed.
Lemma lem7935374 {A : Type'} (h1 : term2 A) : term20 A.
Proof. exact (@lem7935373 A (@lem7933988 A h1)). Qed.
Lemma lem7935375 {A : Type'} (h1 : term2 A) : term17 A.
Proof. exact (@lem7935374 A h1 (@lem7933992 A)). Qed.
Lemma lem7935376 {A : Type'} (h1 : term2 A) : term14 A.
Proof. exact (@lem7935375 A h1 (@lem7933991 A)). Qed.
Lemma lem7935377 {A : Type'} (h1 : term2 A) : term11 A.
Proof. exact (@lem7935376 A h1 (@lem7933989 A)). Qed.
Lemma lem7935378 {A : Type'} (h1 : term2 A) : False.
Proof. exact (@lem7935377 A h1 (@lem7933990 A)). Qed.
Lemma lem7935379 {A : Type'} (h1 : term2 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h2 : term2 A => @lem7935378 A h1) (fun h2 : False => @lem7933988 A h1)). Qed.
Lemma lem7935380 {A : Type'} (h1 : term2 A) : False.
Proof. exact (EQ_MP (@lem7935379 A h1) (@lem7933988 A h1)). Qed.
Lemma lem7935381 {A : Type'} : term1 A.
Proof. exact (fun h0 : term2 A => @lem7935380 A h0). Qed.
Lemma lem7935382 {A : Type'} : @FINITE (tybit0 A) (@UNIV (tybit0 A)).
Proof. exact (EQ_MP (@lem7933987 A) (@lem7935381 A)). Qed.
