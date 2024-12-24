Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INDEX_INJ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDEX_WORKS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18897_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem7609880 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7609881 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7609882 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7609881 t1) (@lem7609880 t1)). Qed.
Lemma lem7609883 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7609882 t1 t2). Qed.
Lemma lem7609884 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7609885 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7609884 t1 t2) (@lem7609883 t1 t2)). Qed.
Lemma lem7609886 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7609885 t1 t2 t3). Qed.
Lemma lem7609887 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7609888 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7609887 t1 t2 t3) (@lem7609886 t1 t2 t3)). Qed.
Lemma lem7609889 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7609888 t1 t2 t3)). Qed.
Lemma lem7609891 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7609892 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem7609891 (term8 A)). Qed.
Lemma lem7609893 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem7609892 A)). Qed.
Lemma lem7609894 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7609901 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem7609902 {A : Type'} : term12 A.
Proof. exact (fun h0 : term11 A => @lem7609901 A h0). Qed.
Lemma lem7609903 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem7609904 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem7609905 {A : Type'} (h1 : term11 A) (h2 : term12 A) : term11 A.
Proof. exact (@lem7609903 A h2 (@lem7609904 A h1)). Qed.
Lemma lem7609906 {A : Type'} (h1 : term11 A) : term13 A.
Proof. exact (fun h0 : term12 A => @lem7609905 A h1 h0). Qed.
Lemma lem7609907 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem7609908 {A : Type'} (h1 : term11 A) (h2 : term12 A) : term11 A.
Proof. exact (@lem7609906 A h1 (@lem7609907 A h2)). Qed.
Lemma lem7609909 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (fun h0 : term11 A => @lem7609908 A h0 h1). Qed.
Lemma lem7609910 {A : Type'} : term14 A.
Proof. exact (fun h0 : term12 A => @lem7609909 A h0). Qed.
Lemma lem7609913 {A : Type'} : term12 A.
Proof. exact (@lem7609910 A (@lem7609902 A)). Qed.
Lemma lem7609914 {A : Type'} : term12 A.
Proof. exact (@lem7609913 A). Qed.
Lemma lem7609934 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7609935 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (@lem7609934 (term17 A)). Qed.
Lemma lem7609944 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (eq_refl (term18 A)). Qed.
Lemma lem7609951 {A : Type'} : (term11 A) = (term19 A).
Proof. exact (MK_COMB (@lem7609944 A) (@lem7609935 A)). Qed.
Lemma lem7609960 {A : Type'} (n : nat) (i : finite_image A) : (term20 A n i) = (term20 A n i).
Proof. exact (eq_refl (term20 A n i)). Qed.
Lemma lem7609961 {A : Type'} (i : finite_image A) : (term21 A i) = (term21 A i).
Proof. exact (fun_ext (fun n : nat => @lem7609960 A n i)). Qed.
Lemma lem7609962 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem7609963 {A : Type'} (i : finite_image A) : (term22 A i) = (term22 A i).
Proof. exact (MK_COMB (@lem7609962) (@lem7609961 A i)). Qed.
Lemma lem7609964 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7609963 A i)). Qed.
Lemma lem7609965 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7609966 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (MK_COMB (@lem7609965 A) (@lem7609964 A)). Qed.
Lemma lem7609967 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7609968 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem7609967) (@lem7609966 A)). Qed.
Lemma lem7609989 {A : Type'} (i : nat) (j : nat) : (term24 A i j) = (term24 A i j).
Proof. exact (eq_refl (term24 A i j)). Qed.
Lemma lem7609990 {A : Type'} (i : nat) : (term25 A i) = (term25 A i).
Proof. exact (fun_ext (fun j : nat => @lem7609989 A i j)). Qed.
Lemma lem7609991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7609992 {A : Type'} (i : nat) : (term26 A i) = (term26 A i).
Proof. exact (MK_COMB (@lem7609991) (@lem7609990 A i)). Qed.
Lemma lem7609993 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun i : nat => @lem7609992 A i)). Qed.
Lemma lem7609994 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7609995 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem7609994) (@lem7609993 A)). Qed.
Lemma lem7609996 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7609997 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7609996) (@lem7609995 A)). Qed.
Lemma lem7609998 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7609999 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem7609998) (@lem7609997 A)). Qed.
Lemma lem7610000 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7609999 A) (@lem7609968 A)). Qed.
Lemma lem7610035 {A : Type'} : (term11 A) = (term19 A).
Proof. exact (TRANS (@lem7609951 A) (@lem7610000 A)). Qed.
Lemma lem7610036 {A : Type'} : (term19 A) = (term11 A).
Proof. exact (SYM (@lem7610035 A)). Qed.
Lemma lem7610037 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7610038 {A : Type'} (h1 : term17 A) : term17 A.
Proof. exact (h1). Qed.
Lemma lem7610066 {A : Type'} (i : nat) (j : nat) : (term28 A i j) = (term29 A i j).
Proof. exact (@lem17646 ((@finite_index A i) = (@finite_index A j)) (i = j)). Qed.
Lemma lem7610068 {A : Type'} (i : nat) (j : nat) : (term30 A i j) = (term30 A i j).
Proof. exact (eq_refl (term30 A i j)). Qed.
Lemma lem7610069 {A : Type'} (i : nat) (j : nat) : (term31 A i j) = (term32 A i j).
Proof. exact (MK_COMB (@lem7610068 A i j) (@lem7610066 A i j)). Qed.
Lemma lem7610070 {A : Type'} (i : nat) (j : nat) : (term33 A i j) = (term31 A i j).
Proof. exact (@lem17362 (term34 A i j) (((@finite_index A i) = (@finite_index A j)) = (i = j))). Qed.
Lemma lem7610071 {A : Type'} (i : nat) (j : nat) : (term33 A i j) = (term32 A i j).
Proof. exact (TRANS (@lem7610070 A i j) (@lem7610069 A i j)). Qed.
Lemma lem7610072 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7610073 {A : Type'} (i : nat) : (term37 A i) = (term38 A i).
Proof. exact (@lem7610072 (term25 A i)). Qed.
Lemma lem7610074 {A : Type'} (i : nat) (j : nat) : (term39 A i j) = (term24 A i j).
Proof. exact (eq_refl (term39 A i j)). Qed.
Lemma lem7610075 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7610076 {A : Type'} (i : nat) (j : nat) : (term40 A i j) = (term33 A i j).
Proof. exact (MK_COMB (@lem7610075) (@lem7610074 A i j)). Qed.
Lemma lem7610077 {A : Type'} (i : nat) (j : nat) : (term40 A i j) = (term32 A i j).
Proof. exact (TRANS (@lem7610076 A i j) (@lem7610071 A i j)). Qed.
Lemma lem7610078 {A : Type'} (i : nat) : (term41 A i) = (term42 A i).
Proof. exact (fun_ext (fun j : nat => @lem7610077 A i j)). Qed.
Lemma lem7610079 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7610080 {A : Type'} (i : nat) : (term38 A i) = (term43 A i).
Proof. exact (MK_COMB (@lem7610079) (@lem7610078 A i)). Qed.
Lemma lem7610081 {A : Type'} (i : nat) : (term37 A i) = (term43 A i).
Proof. exact (TRANS (@lem7610073 A i) (@lem7610080 A i)). Qed.
Lemma lem7610082 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7610083 {A : Type'} : (term10 A) = (term44 A).
Proof. exact (@lem7610082 (term27 A)). Qed.
Lemma lem7610084 {A : Type'} (i : nat) : (term45 A i) = (term26 A i).
Proof. exact (eq_refl (term45 A i)). Qed.
Lemma lem7610085 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7610086 {A : Type'} (i : nat) : (term46 A i) = (term37 A i).
Proof. exact (MK_COMB (@lem7610085) (@lem7610084 A i)). Qed.
Lemma lem7610087 {A : Type'} (i : nat) : (term46 A i) = (term43 A i).
Proof. exact (TRANS (@lem7610086 A i) (@lem7610081 A i)). Qed.
Lemma lem7610088 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (fun_ext (fun i : nat => @lem7610087 A i)). Qed.
Lemma lem7610089 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7610090 {A : Type'} : (term44 A) = (term49 A).
Proof. exact (MK_COMB (@lem7610089) (@lem7610088 A)). Qed.
Lemma lem7610147 {A : Type'} : (term10 A) = (term49 A).
Proof. exact (TRANS (@lem7610083 A) (@lem7610090 A)). Qed.
Lemma lem7610148 {A : Type'} (h1 : term10 A) : term49 A.
Proof. exact (EQ_MP (@lem7610147 A) (@lem7610037 A h1)). Qed.
Lemma lem7610159 {A : Type'} (n : nat) (i : finite_image A) : (term50 A n i) = (term51 A n i).
Proof. exact (@lem17045 (term52 A n) ((@finite_index A n) = i)). Qed.
Lemma lem7610164 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem7610165 {A : Type'} (n : nat) (i : finite_image A) : (term54 A n i) = (term55 A n i).
Proof. exact (MK_COMB (@lem7610164 n) (@lem7610159 A n i)). Qed.
Lemma lem7610166 {A : Type'} (n : nat) (i : finite_image A) : (term56 A n i) = (term54 A n i).
Proof. exact (@lem17045 (term57 n) (term58 A n i)). Qed.
Lemma lem7610167 {A : Type'} (n : nat) (i : finite_image A) : (term56 A n i) = (term55 A n i).
Proof. exact (TRANS (@lem7610166 A n i) (@lem7610165 A n i)). Qed.
Lemma lem7610172 (n' : nat) (n : nat) : (n' = n) = (n' = n).
Proof. exact (eq_refl (n' = n)). Qed.
Lemma lem7610173 {A : Type'} (n : nat) (i : finite_image A) : (term59 A i n) = (term20 A n i).
Proof. exact (eq_refl (term59 A i n)). Qed.
Lemma lem7610174 {A : Type'} (n' : nat) (i : finite_image A) : (term59 A i n') = (term20 A n' i).
Proof. exact (eq_refl (term59 A i n')). Qed.
Lemma lem7610175 {A : Type'} (n' : nat) (i : finite_image A) : (term56 A n' i) = (term55 A n' i).
Proof. exact (@lem7610167 A n' i). Qed.
Lemma lem7610176 (P : nat -> Prop) : (@ex1 nat P) = (term60 P).
Proof. exact (@lem18897 nat P). Qed.
Lemma lem7610177 {A : Type'} (i : finite_image A) : (term22 A i) = (term61 A i).
Proof. exact (@lem7610176 (term21 A i)). Qed.
Lemma lem7610178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7610179 {A : Type'} (n' : nat) (i : finite_image A) : (term62 A i n') = (term56 A n' i).
Proof. exact (MK_COMB (@lem7610178) (@lem7610174 A n' i)). Qed.
Lemma lem7610180 {A : Type'} (n' : nat) (i : finite_image A) : (term62 A i n') = (term55 A n' i).
Proof. exact (TRANS (@lem7610179 A n' i) (@lem7610175 A n' i)). Qed.
Lemma lem7610181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7610182 {A : Type'} (n' : nat) (i : finite_image A) : (term63 A i n') = (term64 A n' i).
Proof. exact (MK_COMB (@lem7610181) (@lem7610180 A n' i)). Qed.
Lemma lem7610183 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term65 A i n' n) = (term66 A i n' n).
Proof. exact (MK_COMB (@lem7610182 A n' i) (@lem7610172 n' n)). Qed.
Lemma lem7610184 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7610185 {A : Type'} (n : nat) (i : finite_image A) : (term62 A i n) = (term56 A n i).
Proof. exact (MK_COMB (@lem7610184) (@lem7610173 A n i)). Qed.
Lemma lem7610186 {A : Type'} (n : nat) (i : finite_image A) : (term62 A i n) = (term55 A n i).
Proof. exact (TRANS (@lem7610185 A n i) (@lem7610167 A n i)). Qed.
Lemma lem7610187 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7610188 {A : Type'} (n : nat) (i : finite_image A) : (term63 A i n) = (term64 A n i).
Proof. exact (MK_COMB (@lem7610187) (@lem7610186 A n i)). Qed.
Lemma lem7610189 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term67 A i n' n) = (term68 A i n' n).
Proof. exact (MK_COMB (@lem7610188 A n i) (@lem7610183 A i n' n)). Qed.
Lemma lem7610190 {A : Type'} (i : finite_image A) (n : nat) : (term69 A i n) = (term70 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7610189 A i n' n)). Qed.
Lemma lem7610191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610192 {A : Type'} (i : finite_image A) (n : nat) : (term71 A i n) = (term72 A i n).
Proof. exact (MK_COMB (@lem7610191) (@lem7610190 A i n)). Qed.
Lemma lem7610193 {A : Type'} (i : finite_image A) : (term73 A i) = (term74 A i).
Proof. exact (fun_ext (fun n : nat => @lem7610192 A i n)). Qed.
Lemma lem7610194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610195 {A : Type'} (i : finite_image A) : (term75 A i) = (term76 A i).
Proof. exact (MK_COMB (@lem7610194) (@lem7610193 A i)). Qed.
Lemma lem7610196 {A : Type'} (n : nat) (i : finite_image A) : (term59 A i n) = (term20 A n i).
Proof. exact (eq_refl (term59 A i n)). Qed.
Lemma lem7610197 {A : Type'} (i : finite_image A) : (term77 A i) = (term21 A i).
Proof. exact (fun_ext (fun n : nat => @lem7610196 A n i)). Qed.
Lemma lem7610198 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7610199 {A : Type'} (i : finite_image A) : (term78 A i) = (term79 A i).
Proof. exact (MK_COMB (@lem7610198) (@lem7610197 A i)). Qed.
Lemma lem7610200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7610201 {A : Type'} (i : finite_image A) : (term80 A i) = (term81 A i).
Proof. exact (MK_COMB (@lem7610200) (@lem7610199 A i)). Qed.
Lemma lem7610202 {A : Type'} (i : finite_image A) : (term61 A i) = (term82 A i).
Proof. exact (MK_COMB (@lem7610201 A i) (@lem7610195 A i)). Qed.
Lemma lem7610203 {A : Type'} (i : finite_image A) : (term22 A i) = (term82 A i).
Proof. exact (TRANS (@lem7610177 A i) (@lem7610202 A i)). Qed.
Lemma lem7610204 {A : Type'} : (term23 A) = (term83 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610203 A i)). Qed.
Lemma lem7610205 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610206 {A : Type'} : (term17 A) = (term84 A).
Proof. exact (MK_COMB (@lem7610205 A) (@lem7610204 A)). Qed.
Lemma lem7610208 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7610209 {A : Type'} (P : type33 A) (Q : type33 A) : (term87 A P Q) = (term88 A P Q).
Proof. exact (@lem7610208 (finite_image A) P Q). Qed.
Lemma lem7610210 {A : Type'} : (term89 A) = (term90 A).
Proof. exact (@lem7610209 A (term91 A) (term92 A)). Qed.
Lemma lem7610211 {A : Type'} (i : finite_image A) : (term93 A i) = (term79 A i).
Proof. exact (eq_refl (term93 A i)). Qed.
Lemma lem7610212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7610213 {A : Type'} (i : finite_image A) : (term94 A i) = (term81 A i).
Proof. exact (MK_COMB (@lem7610212) (@lem7610211 A i)). Qed.
Lemma lem7610214 {A : Type'} (i : finite_image A) : (term95 A i) = (term76 A i).
Proof. exact (eq_refl (term95 A i)). Qed.
Lemma lem7610215 {A : Type'} (i : finite_image A) : (term96 A i) = (term82 A i).
Proof. exact (MK_COMB (@lem7610213 A i) (@lem7610214 A i)). Qed.
Lemma lem7610216 {A : Type'} : (term97 A) = (term83 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610215 A i)). Qed.
Lemma lem7610217 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610218 {A : Type'} : (term89 A) = (term84 A).
Proof. exact (MK_COMB (@lem7610217 A) (@lem7610216 A)). Qed.
Lemma lem7610219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7610220 {A : Type'} : (term98 A) = (term99 A).
Proof. exact (MK_COMB (@lem7610219) (@lem7610218 A)). Qed.
Lemma lem7610221 {A : Type'} (i : finite_image A) : (term93 A i) = (term79 A i).
Proof. exact (eq_refl (term93 A i)). Qed.
Lemma lem7610222 {A : Type'} : (term100 A) = (term91 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610221 A i)). Qed.
Lemma lem7610223 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610224 {A : Type'} : (term101 A) = (term102 A).
Proof. exact (MK_COMB (@lem7610223 A) (@lem7610222 A)). Qed.
Lemma lem7610225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7610226 {A : Type'} : (term103 A) = (term104 A).
Proof. exact (MK_COMB (@lem7610225) (@lem7610224 A)). Qed.
Lemma lem7610227 {A : Type'} (i : finite_image A) : (term95 A i) = (term76 A i).
Proof. exact (eq_refl (term95 A i)). Qed.
Lemma lem7610228 {A : Type'} : (term105 A) = (term92 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610227 A i)). Qed.
Lemma lem7610229 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610230 {A : Type'} : (term106 A) = (term107 A).
Proof. exact (MK_COMB (@lem7610229 A) (@lem7610228 A)). Qed.
Lemma lem7610231 {A : Type'} : (term90 A) = (term108 A).
Proof. exact (MK_COMB (@lem7610226 A) (@lem7610230 A)). Qed.
Lemma lem7610232 {A : Type'} : ((term89 A) = (term90 A)) = ((term84 A) = (term108 A)).
Proof. exact (MK_COMB (@lem7610220 A) (@lem7610231 A)). Qed.
Lemma lem7610233 {A : Type'} : (term84 A) = (term108 A).
Proof. exact (EQ_MP (@lem7610232 A) (@lem7610210 A)). Qed.
Lemma lem7610295 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem7610296 (P : Prop) (Q : nat -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem7610295 nat P Q). Qed.
Lemma lem7610297 {A : Type'} (i : finite_image A) (n : nat) : (term113 A i n) = (term114 A i n).
Proof. exact (@lem7610296 (term55 A n i) (term115 A i n)). Qed.
Lemma lem7610298 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term116 A i n n') = (term66 A i n' n).
Proof. exact (eq_refl (term116 A i n n')). Qed.
Lemma lem7610299 {A : Type'} (n : nat) (i : finite_image A) : (term64 A n i) = (term64 A n i).
Proof. exact (eq_refl (term64 A n i)). Qed.
Lemma lem7610300 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term117 A i n n') = (term68 A i n' n).
Proof. exact (MK_COMB (@lem7610299 A n i) (@lem7610298 A i n' n)). Qed.
Lemma lem7610301 {A : Type'} (i : finite_image A) (n : nat) : (term118 A i n) = (term70 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7610300 A i n' n)). Qed.
Lemma lem7610302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610303 {A : Type'} (i : finite_image A) (n : nat) : (term113 A i n) = (term72 A i n).
Proof. exact (MK_COMB (@lem7610302) (@lem7610301 A i n)). Qed.
Lemma lem7610304 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7610305 {A : Type'} (i : finite_image A) (n : nat) : (term119 A i n) = (term120 A i n).
Proof. exact (MK_COMB (@lem7610304) (@lem7610303 A i n)). Qed.
Lemma lem7610306 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term116 A i n n') = (term66 A i n' n).
Proof. exact (eq_refl (term116 A i n n')). Qed.
Lemma lem7610307 {A : Type'} (i : finite_image A) (n : nat) : (term121 A i n) = (term115 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7610306 A i n' n)). Qed.
Lemma lem7610308 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610309 {A : Type'} (i : finite_image A) (n : nat) : (term122 A i n) = (term123 A i n).
Proof. exact (MK_COMB (@lem7610308) (@lem7610307 A i n)). Qed.
Lemma lem7610310 {A : Type'} (n : nat) (i : finite_image A) : (term64 A n i) = (term64 A n i).
Proof. exact (eq_refl (term64 A n i)). Qed.
Lemma lem7610311 {A : Type'} (i : finite_image A) (n : nat) : (term114 A i n) = (term124 A i n).
Proof. exact (MK_COMB (@lem7610310 A n i) (@lem7610309 A i n)). Qed.
Lemma lem7610312 {A : Type'} (i : finite_image A) (n : nat) : ((term113 A i n) = (term114 A i n)) = ((term72 A i n) = (term124 A i n)).
Proof. exact (MK_COMB (@lem7610305 A i n) (@lem7610311 A i n)). Qed.
Lemma lem7610313 {A : Type'} (i : finite_image A) (n : nat) : (term72 A i n) = (term124 A i n).
Proof. exact (EQ_MP (@lem7610312 A i n) (@lem7610297 A i n)). Qed.
Lemma lem7610362 {A : Type'} (i : finite_image A) : (term74 A i) = (term125 A i).
Proof. exact (fun_ext (fun n : nat => @lem7610313 A i n)). Qed.
Lemma lem7610363 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610364 {A : Type'} (i : finite_image A) : (term76 A i) = (term126 A i).
Proof. exact (MK_COMB (@lem7610363) (@lem7610362 A i)). Qed.
Lemma lem7610413 {A : Type'} : (term92 A) = (term127 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610364 A i)). Qed.
Lemma lem7610414 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610415 {A : Type'} : (term107 A) = (term128 A).
Proof. exact (MK_COMB (@lem7610414 A) (@lem7610413 A)). Qed.
Lemma lem7610420 {A : Type'} : (term104 A) = (term104 A).
Proof. exact (eq_refl (term104 A)). Qed.
Lemma lem7610421 {A : Type'} : (term108 A) = (term129 A).
Proof. exact (MK_COMB (@lem7610420 A) (@lem7610415 A)). Qed.
Lemma lem7610422 {A : Type'} : (term84 A) = (term129 A).
Proof. exact (TRANS (@lem7610233 A) (@lem7610421 A)). Qed.
Lemma lem7610424 {A B : Type'} (P : type1413 A B) : (term130 A B P) = (term131 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7610425 {A : Type'} (P : type32 A) : (term132 A P) = (term133 A P).
Proof. exact (@lem7610424 (finite_image A) nat P). Qed.
Lemma lem7610426 {A : Type'} : (term134 A) = (term135 A).
Proof. exact (@lem7610425 A (term136 A)). Qed.
Lemma lem7610427 {A : Type'} (i : finite_image A) : (term137 A i) = (term21 A i).
Proof. exact (eq_refl (term137 A i)). Qed.
Lemma lem7610428 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7610429 {A : Type'} (i : finite_image A) (n : nat) : (term138 A i n) = (term59 A i n).
Proof. exact (MK_COMB (@lem7610427 A i) (@lem7610428 n)). Qed.
Lemma lem7610430 {A : Type'} (n : nat) (i : finite_image A) : (term59 A i n) = (term20 A n i).
Proof. exact (eq_refl (term59 A i n)). Qed.
Lemma lem7610431 {A : Type'} (n : nat) (i : finite_image A) : (term138 A i n) = (term20 A n i).
Proof. exact (TRANS (@lem7610429 A i n) (@lem7610430 A n i)). Qed.
Lemma lem7610432 {A : Type'} (i : finite_image A) : (term139 A i) = (term21 A i).
Proof. exact (fun_ext (fun n : nat => @lem7610431 A n i)). Qed.
Lemma lem7610433 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7610434 {A : Type'} (i : finite_image A) : (term140 A i) = (term79 A i).
Proof. exact (MK_COMB (@lem7610433) (@lem7610432 A i)). Qed.
Lemma lem7610435 {A : Type'} : (term141 A) = (term91 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610434 A i)). Qed.
Lemma lem7610436 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610437 {A : Type'} : (term134 A) = (term102 A).
Proof. exact (MK_COMB (@lem7610436 A) (@lem7610435 A)). Qed.
Lemma lem7610438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7610439 {A : Type'} : (term142 A) = (term143 A).
Proof. exact (MK_COMB (@lem7610438) (@lem7610437 A)). Qed.
Lemma lem7610440 {A : Type'} (i : finite_image A) : (term137 A i) = (term21 A i).
Proof. exact (eq_refl (term137 A i)). Qed.
Lemma lem7610441 {A : Type'} (n : type34 A) (i : finite_image A) : (n i) = (n i).
Proof. exact (eq_refl (n i)). Qed.
Lemma lem7610442 {A : Type'} (n : type34 A) (i : finite_image A) : (term144 A n i) = (term145 A n i).
Proof. exact (MK_COMB (@lem7610440 A i) (@lem7610441 A n i)). Qed.
Lemma lem7610443 {A : Type'} (n : type34 A) (i : finite_image A) : (term145 A n i) = (term146 A n i).
Proof. exact (eq_refl (term145 A n i)). Qed.
Lemma lem7610444 {A : Type'} (n : type34 A) (i : finite_image A) : (term144 A n i) = (term146 A n i).
Proof. exact (TRANS (@lem7610442 A n i) (@lem7610443 A n i)). Qed.
Lemma lem7610445 {A : Type'} (n : type34 A) : (term147 A n) = (term148 A n).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610444 A n i)). Qed.
Lemma lem7610446 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610447 {A : Type'} (n : type34 A) : (term149 A n) = (term150 A n).
Proof. exact (MK_COMB (@lem7610446 A) (@lem7610445 A n)). Qed.
Lemma lem7610448 {A : Type'} : (term151 A) = (term152 A).
Proof. exact (fun_ext (fun n : type34 A => @lem7610447 A n)). Qed.
Lemma lem7610449 {A : Type'} : (@ex ((finite_image A) -> nat)) = (@ex ((finite_image A) -> nat)).
Proof. exact (eq_refl (@ex ((finite_image A) -> nat))). Qed.
Lemma lem7610450 {A : Type'} : (term135 A) = (term153 A).
Proof. exact (MK_COMB (@lem7610449 A) (@lem7610448 A)). Qed.
Lemma lem7610451 {A : Type'} : ((term134 A) = (term135 A)) = ((term102 A) = (term153 A)).
Proof. exact (MK_COMB (@lem7610439 A) (@lem7610450 A)). Qed.
Lemma lem7610452 {A : Type'} : (term102 A) = (term153 A).
Proof. exact (EQ_MP (@lem7610451 A) (@lem7610426 A)). Qed.
Lemma lem7610453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7610454 {A : Type'} : (term104 A) = (term154 A).
Proof. exact (MK_COMB (@lem7610453) (@lem7610452 A)). Qed.
Lemma lem7610455 {A : Type'} : (term128 A) = (term128 A).
Proof. exact (eq_refl (term128 A)). Qed.
Lemma lem7610456 {A : Type'} : (term129 A) = (term155 A).
Proof. exact (MK_COMB (@lem7610454 A) (@lem7610455 A)). Qed.
Lemma lem7610458 {A : Type'} (P : A -> Prop) (Q : Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7610459 {A : Type'} (P : type60 A) (Q : Prop) : (term158 A P Q) = (term159 A P Q).
Proof. exact (@lem7610458 (type34 A) P Q). Qed.
Lemma lem7610460 {A : Type'} : (term160 A) = (term161 A).
Proof. exact (@lem7610459 A (term152 A) (term128 A)). Qed.
Lemma lem7610461 {A : Type'} (n : type34 A) : (term162 A n) = (term150 A n).
Proof. exact (eq_refl (term162 A n)). Qed.
Lemma lem7610462 {A : Type'} : (term163 A) = (term152 A).
Proof. exact (fun_ext (fun n : type34 A => @lem7610461 A n)). Qed.
Lemma lem7610463 {A : Type'} : (@ex ((finite_image A) -> nat)) = (@ex ((finite_image A) -> nat)).
Proof. exact (eq_refl (@ex ((finite_image A) -> nat))). Qed.
Lemma lem7610464 {A : Type'} : (term164 A) = (term153 A).
Proof. exact (MK_COMB (@lem7610463 A) (@lem7610462 A)). Qed.
Lemma lem7610465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7610466 {A : Type'} : (term165 A) = (term154 A).
Proof. exact (MK_COMB (@lem7610465) (@lem7610464 A)). Qed.
Lemma lem7610467 {A : Type'} : (term128 A) = (term128 A).
Proof. exact (eq_refl (term128 A)). Qed.
Lemma lem7610468 {A : Type'} : (term160 A) = (term155 A).
Proof. exact (MK_COMB (@lem7610466 A) (@lem7610467 A)). Qed.
Lemma lem7610469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7610470 {A : Type'} : (term166 A) = (term167 A).
Proof. exact (MK_COMB (@lem7610469) (@lem7610468 A)). Qed.
Lemma lem7610471 {A : Type'} (n : type34 A) : (term162 A n) = (term150 A n).
Proof. exact (eq_refl (term162 A n)). Qed.
Lemma lem7610472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7610473 {A : Type'} (n : type34 A) : (term168 A n) = (term169 A n).
Proof. exact (MK_COMB (@lem7610472) (@lem7610471 A n)). Qed.
Lemma lem7610474 {A : Type'} : (term128 A) = (term128 A).
Proof. exact (eq_refl (term128 A)). Qed.
Lemma lem7610475 {A : Type'} (n : type34 A) : (term170 A n) = (term171 A n).
Proof. exact (MK_COMB (@lem7610473 A n) (@lem7610474 A)). Qed.
Lemma lem7610476 {A : Type'} : (term172 A) = (term173 A).
Proof. exact (fun_ext (fun n : type34 A => @lem7610475 A n)). Qed.
Lemma lem7610477 {A : Type'} : (@ex ((finite_image A) -> nat)) = (@ex ((finite_image A) -> nat)).
Proof. exact (eq_refl (@ex ((finite_image A) -> nat))). Qed.
Lemma lem7610478 {A : Type'} : (term161 A) = (term174 A).
Proof. exact (MK_COMB (@lem7610477 A) (@lem7610476 A)). Qed.
Lemma lem7610479 {A : Type'} : ((term160 A) = (term161 A)) = ((term155 A) = (term174 A)).
Proof. exact (MK_COMB (@lem7610470 A) (@lem7610478 A)). Qed.
Lemma lem7610480 {A : Type'} : (term155 A) = (term174 A).
Proof. exact (EQ_MP (@lem7610479 A) (@lem7610460 A)). Qed.
Lemma lem7610481 {A : Type'} : (term129 A) = (term174 A).
Proof. exact (TRANS (@lem7610456 A) (@lem7610480 A)). Qed.
Lemma lem7610482 {A : Type'} : (term84 A) = (term174 A).
Proof. exact (TRANS (@lem7610422 A) (@lem7610481 A)). Qed.
Lemma lem7610483 {A : Type'} : (term17 A) = (term174 A).
Proof. exact (TRANS (@lem7610206 A) (@lem7610482 A)). Qed.
Lemma lem7610484 {A : Type'} (h1 : term17 A) : term174 A.
Proof. exact (EQ_MP (@lem7610483 A) (@lem7610038 A h1)). Qed.
Lemma lem7610485 {A : Type'} (n : type34 A) (h1 : term171 A n) : term171 A n.
Proof. exact (h1). Qed.
Lemma lem7610486 {A : Type'} (i : nat) (h1 : term43 A i) : term43 A i.
Proof. exact (h1). Qed.
Lemma lem7610530 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term66 A i n' n) = (term66 A i n' n).
Proof. exact (eq_refl (term66 A i n' n)). Qed.
Lemma lem7610531 {A : Type'} (i : finite_image A) (n : nat) : (term115 A i n) = (term115 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7610530 A i n' n)). Qed.
Lemma lem7610532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610533 {A : Type'} (i : finite_image A) (n : nat) : (term123 A i n) = (term123 A i n).
Proof. exact (MK_COMB (@lem7610532) (@lem7610531 A i n)). Qed.
Lemma lem7610570 {A : Type'} (n : nat) (i : finite_image A) : (term64 A n i) = (term64 A n i).
Proof. exact (eq_refl (term64 A n i)). Qed.
Lemma lem7610571 {A : Type'} (i : finite_image A) (n : nat) : (term124 A i n) = (term124 A i n).
Proof. exact (MK_COMB (@lem7610570 A n i) (@lem7610533 A i n)). Qed.
Lemma lem7610572 {A : Type'} (i : finite_image A) : (term125 A i) = (term125 A i).
Proof. exact (fun_ext (fun n : nat => @lem7610571 A i n)). Qed.
Lemma lem7610573 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610574 {A : Type'} (i : finite_image A) : (term126 A i) = (term126 A i).
Proof. exact (MK_COMB (@lem7610573) (@lem7610572 A i)). Qed.
Lemma lem7610575 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610574 A i)). Qed.
Lemma lem7610576 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610577 {A : Type'} : (term128 A) = (term128 A).
Proof. exact (MK_COMB (@lem7610576 A) (@lem7610575 A)). Qed.
Lemma lem7610612 {A : Type'} (n : type34 A) (i : finite_image A) : (term146 A n i) = (term146 A n i).
Proof. exact (eq_refl (term146 A n i)). Qed.
Lemma lem7610613 {A : Type'} (n : type34 A) : (term148 A n) = (term148 A n).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610612 A n i)). Qed.
Lemma lem7610614 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610615 {A : Type'} (n : type34 A) : (term150 A n) = (term150 A n).
Proof. exact (MK_COMB (@lem7610614 A) (@lem7610613 A n)). Qed.
Lemma lem7610616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7610617 {A : Type'} (n : type34 A) : (term169 A n) = (term169 A n).
Proof. exact (MK_COMB (@lem7610616) (@lem7610615 A n)). Qed.
Lemma lem7610618 {A : Type'} (n : type34 A) : (term171 A n) = (term171 A n).
Proof. exact (MK_COMB (@lem7610617 A n) (@lem7610577 A)). Qed.
Lemma lem7610619 {A : Type'} (n : type34 A) (h1 : term171 A n) : term171 A n.
Proof. exact (EQ_MP (@lem7610618 A n) (@lem7610485 A n h1)). Qed.
Lemma lem7610705 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term32 A i j.
Proof. exact (h1). Qed.
Lemma lem7610706 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term29 A i j.
Proof. exact (proj2 (@lem7610705 A i j h1)). Qed.
Lemma lem7610707 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term34 A i j.
Proof. exact (proj1 (@lem7610705 A i j h1)). Qed.
Lemma lem7610708 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term175 A i j.
Proof. exact (proj2 (@lem7610707 A i j h1)). Qed.
Lemma lem7610710 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term176 A j.
Proof. exact (proj2 (@lem7610708 A i j h1)). Qed.
Lemma lem7610714 {A : Type'} (n : type34 A) (h1 : term171 A n) : term128 A.
Proof. exact (proj2 (@lem7610619 A n h1)). Qed.
Lemma lem7610716 {A : Type'} (i : nat) (j : nat) (h1 : term177 A i j) : term177 A i j.
Proof. exact (h1). Qed.
Lemma lem7610717 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : term178 A i j.
Proof. exact (h1). Qed.
Lemma lem7610754 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7610755 (P : Prop) (Q : nat -> Prop) : (term112 P Q) = (term111 P Q).
Proof. exact (@lem7610754 nat P Q). Qed.
Lemma lem7610756 {A : Type'} (i : finite_image A) (n : nat) : (term114 A i n) = (term113 A i n).
Proof. exact (@lem7610755 (term55 A n i) (term115 A i n)). Qed.
Lemma lem7610757 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term116 A i n n') = (term66 A i n' n).
Proof. exact (eq_refl (term116 A i n n')). Qed.
Lemma lem7610758 {A : Type'} (i : finite_image A) (n : nat) : (term121 A i n) = (term115 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7610757 A i n' n)). Qed.
Lemma lem7610759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610760 {A : Type'} (i : finite_image A) (n : nat) : (term122 A i n) = (term123 A i n).
Proof. exact (MK_COMB (@lem7610759) (@lem7610758 A i n)). Qed.
Lemma lem7610761 {A : Type'} (n : nat) (i : finite_image A) : (term64 A n i) = (term64 A n i).
Proof. exact (eq_refl (term64 A n i)). Qed.
Lemma lem7610762 {A : Type'} (i : finite_image A) (n : nat) : (term114 A i n) = (term124 A i n).
Proof. exact (MK_COMB (@lem7610761 A n i) (@lem7610760 A i n)). Qed.
Lemma lem7610763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7610764 {A : Type'} (i : finite_image A) (n : nat) : (term179 A i n) = (term180 A i n).
Proof. exact (MK_COMB (@lem7610763) (@lem7610762 A i n)). Qed.
Lemma lem7610765 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term116 A i n n') = (term66 A i n' n).
Proof. exact (eq_refl (term116 A i n n')). Qed.
Lemma lem7610766 {A : Type'} (n : nat) (i : finite_image A) : (term64 A n i) = (term64 A n i).
Proof. exact (eq_refl (term64 A n i)). Qed.
Lemma lem7610767 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term117 A i n n') = (term68 A i n' n).
Proof. exact (MK_COMB (@lem7610766 A n i) (@lem7610765 A i n' n)). Qed.
Lemma lem7610768 {A : Type'} (i : finite_image A) (n : nat) : (term118 A i n) = (term70 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7610767 A i n' n)). Qed.
Lemma lem7610769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610770 {A : Type'} (i : finite_image A) (n : nat) : (term113 A i n) = (term72 A i n).
Proof. exact (MK_COMB (@lem7610769) (@lem7610768 A i n)). Qed.
Lemma lem7610771 {A : Type'} (i : finite_image A) (n : nat) : ((term114 A i n) = (term113 A i n)) = ((term124 A i n) = (term72 A i n)).
Proof. exact (MK_COMB (@lem7610764 A i n) (@lem7610770 A i n)). Qed.
Lemma lem7610772 {A : Type'} (i : finite_image A) (n : nat) : (term124 A i n) = (term72 A i n).
Proof. exact (EQ_MP (@lem7610771 A i n) (@lem7610756 A i n)). Qed.
Lemma lem7610773 {A : Type'} (i : finite_image A) : (term125 A i) = (term74 A i).
Proof. exact (fun_ext (fun n : nat => @lem7610772 A i n)). Qed.
Lemma lem7610774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610775 {A : Type'} (i : finite_image A) : (term126 A i) = (term76 A i).
Proof. exact (MK_COMB (@lem7610774) (@lem7610773 A i)). Qed.
Lemma lem7610776 {A : Type'} : (term127 A) = (term92 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610775 A i)). Qed.
Lemma lem7610777 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610778 {A : Type'} : (term128 A) = (term107 A).
Proof. exact (MK_COMB (@lem7610777 A) (@lem7610776 A)). Qed.
Lemma lem7610815 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term68 A i n' n) = (term68 A i n' n).
Proof. exact (eq_refl (term68 A i n' n)). Qed.
Lemma lem7610816 {A : Type'} (i : finite_image A) (n : nat) : (term70 A i n) = (term70 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7610815 A i n' n)). Qed.
Lemma lem7610817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610818 {A : Type'} (i : finite_image A) (n : nat) : (term72 A i n) = (term72 A i n).
Proof. exact (MK_COMB (@lem7610817) (@lem7610816 A i n)). Qed.
Lemma lem7610819 {A : Type'} (i : finite_image A) : (term74 A i) = (term74 A i).
Proof. exact (fun_ext (fun n : nat => @lem7610818 A i n)). Qed.
Lemma lem7610820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7610821 {A : Type'} (i : finite_image A) : (term76 A i) = (term76 A i).
Proof. exact (MK_COMB (@lem7610820) (@lem7610819 A i)). Qed.
Lemma lem7610822 {A : Type'} : (term92 A) = (term92 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7610821 A i)). Qed.
Lemma lem7610823 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7610824 {A : Type'} : (term107 A) = (term107 A).
Proof. exact (MK_COMB (@lem7610823 A) (@lem7610822 A)). Qed.
Lemma lem7610825 {A : Type'} : (term128 A) = (term107 A).
Proof. exact (TRANS (@lem7610778 A) (@lem7610824 A)). Qed.
Lemma lem7610826 {A : Type'} (n : type34 A) (h1 : term171 A n) : term107 A.
Proof. exact (EQ_MP (@lem7610825 A) (@lem7610714 A n h1)). Qed.
Lemma lem7610951 {A : Type'} (_97912 : finite_image A) (n : type34 A) (h1 : term171 A n) : term95 A _97912.
Proof. exact (@lem7610826 A n h1 _97912). Qed.
Lemma lem7610952 {A : Type'} (_97912 : finite_image A) : (term95 A _97912) = (term76 A _97912).
Proof. exact (eq_refl (term95 A _97912)). Qed.
Lemma lem7610953 {A : Type'} (_97912 : finite_image A) (n : type34 A) (h1 : term171 A n) : term76 A _97912.
Proof. exact (EQ_MP (@lem7610952 A _97912) (@lem7610951 A _97912 n h1)). Qed.
Lemma lem7610954 {A : Type'} (_97912 : finite_image A) (_97913 : nat) (n : type34 A) (h1 : term171 A n) : term181 A _97912 _97913.
Proof. exact (@lem7610953 A _97912 n h1 _97913). Qed.
Lemma lem7610955 {A : Type'} (_97912 : finite_image A) (_97913 : nat) : (term181 A _97912 _97913) = (term72 A _97912 _97913).
Proof. exact (eq_refl (term181 A _97912 _97913)). Qed.
Lemma lem7610956 {A : Type'} (_97912 : finite_image A) (_97913 : nat) (n : type34 A) (h1 : term171 A n) : term72 A _97912 _97913.
Proof. exact (EQ_MP (@lem7610955 A _97912 _97913) (@lem7610954 A _97912 _97913 n h1)). Qed.
Lemma lem7610957 {A : Type'} (_97912 : finite_image A) (_97913 : nat) (_97914 : nat) (n : type34 A) (h1 : term171 A n) : term182 A _97912 _97913 _97914.
Proof. exact (@lem7610956 A _97912 _97913 n h1 _97914). Qed.
Lemma lem7610958 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term182 A _97912 _97913 _97914) = (term68 A _97912 _97914 _97913).
Proof. exact (eq_refl (term182 A _97912 _97913 _97914)). Qed.
Lemma lem7610959 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) (n : type34 A) (h1 : term171 A n) : term68 A _97912 _97914 _97913.
Proof. exact (EQ_MP (@lem7610958 A _97912 _97914 _97913) (@lem7610957 A _97912 _97913 _97914 n h1)). Qed.
Lemma lem7610991 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term66 A _97912 _97914 _97913) = (term183 A _97912 _97914 _97913).
Proof. exact (@lem7609889 (term184 _97914) (term51 A _97914 _97912) (_97914 = _97913)). Qed.
Lemma lem7610998 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term185 A _97912 _97914 _97913) = (term186 A _97912 _97914 _97913).
Proof. exact (@lem7609889 (term187 A _97914) (term188 A _97914 _97912) (_97914 = _97913)). Qed.
Lemma lem7610999 (_97914 : nat) : (term53 _97914) = (term53 _97914).
Proof. exact (eq_refl (term53 _97914)). Qed.
Lemma lem7611002 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term183 A _97912 _97914 _97913) = (term189 A _97912 _97914 _97913).
Proof. exact (MK_COMB (@lem7610999 _97914) (@lem7610998 A _97912 _97914 _97913)). Qed.
Lemma lem7611004 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term66 A _97912 _97914 _97913) = (term189 A _97912 _97914 _97913).
Proof. exact (TRANS (@lem7610991 A _97912 _97914 _97913) (@lem7611002 A _97912 _97914 _97913)). Qed.
Lemma lem7611005 {A : Type'} (_97913 : nat) (_97912 : finite_image A) : (term64 A _97913 _97912) = (term64 A _97913 _97912).
Proof. exact (eq_refl (term64 A _97913 _97912)). Qed.
Lemma lem7611006 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term68 A _97912 _97914 _97913) = (term190 A _97912 _97914 _97913).
Proof. exact (MK_COMB (@lem7611005 A _97913 _97912) (@lem7611004 A _97912 _97914 _97913)). Qed.
Lemma lem7611007 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term190 A _97912 _97914 _97913) = (term191 A _97912 _97914 _97913).
Proof. exact (@lem7609889 (term184 _97913) (term51 A _97913 _97912) (term189 A _97912 _97914 _97913)). Qed.
Lemma lem7611014 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term192 A _97912 _97914 _97913) = (term193 A _97912 _97914 _97913).
Proof. exact (@lem7609889 (term187 A _97913) (term188 A _97913 _97912) (term189 A _97912 _97914 _97913)). Qed.
Lemma lem7611015 (_97913 : nat) : (term53 _97913) = (term53 _97913).
Proof. exact (eq_refl (term53 _97913)). Qed.
Lemma lem7611018 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term191 A _97912 _97914 _97913) = (term194 A _97912 _97914 _97913).
Proof. exact (MK_COMB (@lem7611015 _97913) (@lem7611014 A _97912 _97914 _97913)). Qed.
Lemma lem7611019 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term190 A _97912 _97914 _97913) = (term194 A _97912 _97914 _97913).
Proof. exact (TRANS (@lem7611007 A _97912 _97914 _97913) (@lem7611018 A _97912 _97914 _97913)). Qed.
Lemma lem7611020 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term68 A _97912 _97914 _97913) = (term194 A _97912 _97914 _97913).
Proof. exact (TRANS (@lem7611006 A _97912 _97914 _97913) (@lem7611019 A _97912 _97914 _97913)). Qed.
Lemma lem7611021 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) (n : type34 A) (h1 : term171 A n) : term194 A _97912 _97914 _97913.
Proof. exact (EQ_MP (@lem7611020 A _97912 _97914 _97913) (@lem7610959 A _97912 _97914 _97913 n h1)). Qed.
Lemma lem7611025 {A : Type'} (i : nat) (j : nat) (h1 : term177 A i j) : term195 i j.
Proof. exact (proj2 (@lem7610716 A i j h1)). Qed.
Lemma lem7611075 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : term196 A i j.
Proof. exact (proj1 (@lem7610717 A i j h1)). Qed.
Lemma lem7611077 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : i = j.
Proof. exact (proj2 (@lem7610717 A i j h1)). Qed.
Lemma lem7611166 {A : Type'} (j : nat) : (term197 A j) = (term197 A j).
Proof. exact (eq_refl (term197 A j)). Qed.
Lemma lem7611167 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : (term198 A j i) = (term199 A j).
Proof. exact (MK_COMB (@lem7611166 A j) (@lem7611077 A i j h1)). Qed.
Lemma lem7611168 {A : Type'} (j : nat) : (term199 A j) = (term200 A j).
Proof. exact (eq_refl (term199 A j)). Qed.
Lemma lem7611169 {A : Type'} (j : nat) (i : nat) : (term201 A j i) = (term201 A j i).
Proof. exact (eq_refl (term201 A j i)). Qed.
Lemma lem7611170 {A : Type'} (i : nat) (j : nat) : ((term198 A j i) = (term199 A j)) = ((term198 A j i) = (term200 A j)).
Proof. exact (MK_COMB (@lem7611169 A j i) (@lem7611168 A j)). Qed.
Lemma lem7611171 {A : Type'} (i : nat) (j : nat) : (term198 A j i) = (term196 A i j).
Proof. exact (eq_refl (term198 A j i)). Qed.
Lemma lem7611172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7611173 {A : Type'} (i : nat) (j : nat) : (term201 A j i) = (term202 A i j).
Proof. exact (MK_COMB (@lem7611172) (@lem7611171 A i j)). Qed.
Lemma lem7611174 {A : Type'} (j : nat) : (term200 A j) = (term200 A j).
Proof. exact (eq_refl (term200 A j)). Qed.
Lemma lem7611175 {A : Type'} (i : nat) (j : nat) : ((term198 A j i) = (term200 A j)) = ((term196 A i j) = (term200 A j)).
Proof. exact (MK_COMB (@lem7611173 A i j) (@lem7611174 A j)). Qed.
Lemma lem7611176 {A : Type'} (i : nat) (j : nat) : ((term198 A j i) = (term199 A j)) = ((term196 A i j) = (term200 A j)).
Proof. exact (TRANS (@lem7611170 A i j) (@lem7611175 A i j)). Qed.
Lemma lem7611177 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : (term196 A i j) = (term200 A j).
Proof. exact (EQ_MP (@lem7611176 A i j) (@lem7611167 A i j h1)). Qed.
Lemma lem7611178 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : term200 A j.
Proof. exact (EQ_MP (@lem7611177 A i j h1) (@lem7611075 A i j h1)). Qed.
Lemma lem7611287 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term57 j.
Proof. exact (proj1 (@lem7610710 A i j h1)). Qed.
Lemma lem7611288 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term203 j.
Proof. exact (fun h0 : term184 j => @lem7611287 A i j h1). Qed.
Lemma lem7611290 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7611291 (j : nat) : (term203 j) = (term57 j).
Proof. exact (@lem7611290 (term57 j)). Qed.
Lemma lem7611292 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term57 j.
Proof. exact (EQ_MP (@lem7611291 j) (@lem7611288 A i j h1)). Qed.
Lemma lem7611294 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term52 A j.
Proof. exact (proj2 (@lem7610710 A i j h1)). Qed.
Lemma lem7611295 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term205 A j.
Proof. exact (fun h0 : term187 A j => @lem7611294 A i j h1). Qed.
Lemma lem7611297 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7611298 {A : Type'} (j : nat) : (term205 A j) = (term52 A j).
Proof. exact (@lem7611297 (term52 A j)). Qed.
Lemma lem7611299 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term52 A j.
Proof. exact (EQ_MP (@lem7611298 A j) (@lem7611295 A i j h1)). Qed.
Lemma lem7611301 {A : Type'} (x : finite_image A) : x = x.
Proof. exact (@lem21386 (finite_image A) x). Qed.
Lemma lem7611302 {A : Type'} (x : finite_image A) : x = x.
Proof. exact (@lem7611301 A x). Qed.
Lemma lem7611303 {A : Type'} (j : nat) : (@finite_index A j) = (@finite_index A j).
Proof. exact (@lem7611302 A (@finite_index A j)). Qed.
Lemma lem7611304 {A : Type'} (j : nat) : term206 A j.
Proof. exact (fun h0 : term200 A j => @lem7611303 A j). Qed.
Lemma lem7611306 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7611307 {A : Type'} (j : nat) : (term206 A j) = ((@finite_index A j) = (@finite_index A j)).
Proof. exact (@lem7611306 ((@finite_index A j) = (@finite_index A j))). Qed.
Lemma lem7611308 {A : Type'} (j : nat) : (@finite_index A j) = (@finite_index A j).
Proof. exact (EQ_MP (@lem7611307 A j) (@lem7611304 A j)). Qed.
Lemma lem7611310 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term57 i.
Proof. exact (proj1 (@lem7610707 A i j h1)). Qed.
Lemma lem7611311 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term203 i.
Proof. exact (fun h0 : term184 i => @lem7611310 A i j h1). Qed.
Lemma lem7611313 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7611314 (i : nat) : (term203 i) = (term57 i).
Proof. exact (@lem7611313 (term57 i)). Qed.
Lemma lem7611315 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term57 i.
Proof. exact (EQ_MP (@lem7611314 i) (@lem7611311 A i j h1)). Qed.
Lemma lem7611317 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term52 A i.
Proof. exact (proj1 (@lem7610708 A i j h1)). Qed.
Lemma lem7611318 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term205 A i.
Proof. exact (fun h0 : term187 A i => @lem7611317 A i j h1). Qed.
Lemma lem7611320 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7611321 {A : Type'} (i : nat) : (term205 A i) = (term52 A i).
Proof. exact (@lem7611320 (term52 A i)). Qed.
Lemma lem7611322 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) : term52 A i.
Proof. exact (EQ_MP (@lem7611321 A i) (@lem7611318 A i j h1)). Qed.
Lemma lem7611324 {A : Type'} (i : nat) (j : nat) (h1 : term177 A i j) : (@finite_index A i) = (@finite_index A j).
Proof. exact (proj1 (@lem7610716 A i j h1)). Qed.
Lemma lem7611325 {A : Type'} (i : nat) (j : nat) (h1 : term177 A i j) : term207 A i j.
Proof. exact (fun h0 : term196 A i j => @lem7611324 A i j h1). Qed.
Lemma lem7611327 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7611328 {A : Type'} (i : nat) (j : nat) : (term207 A i j) = ((@finite_index A i) = (@finite_index A j)).
Proof. exact (@lem7611327 ((@finite_index A i) = (@finite_index A j))). Qed.
Lemma lem7611329 {A : Type'} (i : nat) (j : nat) (h1 : term177 A i j) : (@finite_index A i) = (@finite_index A j).
Proof. exact (EQ_MP (@lem7611328 A i j) (@lem7611325 A i j h1)). Qed.
Lemma lem7611335 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611336 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term194 A _97912 _97914 _97913) = (term208 A _97912 _97914 _97913).
Proof. exact (@lem7611335 (term187 A _97913) (term184 _97913) (term209 A _97912 _97914 _97913)). Qed.
Lemma lem7611360 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611361 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term209 A _97912 _97914 _97913) = (term210 A _97912 _97914 _97913).
Proof. exact (@lem7611360 (term184 _97914) (term188 A _97913 _97912) (term186 A _97912 _97914 _97913)). Qed.
Lemma lem7611375 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611376 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term211 A _97912 _97914 _97913) = (term212 A _97912 _97914 _97913).
Proof. exact (@lem7611375 (term187 A _97914) (term188 A _97913 _97912) (term213 A _97912 _97914 _97913)). Qed.
Lemma lem7611402 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7611403 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term213 A _97912 _97914 _97913) = (term214 A _97913 _97914 _97912).
Proof. exact (@lem7611402 (_97914 = _97913) (term188 A _97914 _97912)). Qed.
Lemma lem7611413 {A : Type'} (_97913 : nat) (_97912 : finite_image A) : (term215 A _97913 _97912) = (term215 A _97913 _97912).
Proof. exact (eq_refl (term215 A _97913 _97912)). Qed.
Lemma lem7611414 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term216 A _97912 _97914 _97913) = (term217 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611413 A _97913 _97912) (@lem7611403 A _97913 _97914 _97912)). Qed.
Lemma lem7611418 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611419 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term217 A _97913 _97914 _97912) = (term218 A _97913 _97914 _97912).
Proof. exact (@lem7611418 (_97914 = _97913) (term188 A _97913 _97912) (term188 A _97914 _97912)). Qed.
Lemma lem7611441 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term216 A _97912 _97914 _97913) = (term218 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611414 A _97913 _97914 _97912) (@lem7611419 A _97913 _97914 _97912)). Qed.
Lemma lem7611442 {A : Type'} (_97914 : nat) : (term219 A _97914) = (term219 A _97914).
Proof. exact (eq_refl (term219 A _97914)). Qed.
Lemma lem7611443 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term212 A _97912 _97914 _97913) = (term220 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611442 A _97914) (@lem7611441 A _97913 _97914 _97912)). Qed.
Lemma lem7611447 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611448 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term220 A _97913 _97914 _97912) = (term221 A _97913 _97914 _97912).
Proof. exact (@lem7611447 (_97914 = _97913) (term187 A _97914) (term222 A _97913 _97914 _97912)). Qed.
Lemma lem7611480 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term212 A _97912 _97914 _97913) = (term221 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611443 A _97913 _97914 _97912) (@lem7611448 A _97913 _97914 _97912)). Qed.
Lemma lem7611481 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term211 A _97912 _97914 _97913) = (term221 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611376 A _97912 _97914 _97913) (@lem7611480 A _97913 _97914 _97912)). Qed.
Lemma lem7611482 (_97914 : nat) : (term53 _97914) = (term53 _97914).
Proof. exact (eq_refl (term53 _97914)). Qed.
Lemma lem7611483 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term210 A _97912 _97914 _97913) = (term223 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611482 _97914) (@lem7611481 A _97913 _97914 _97912)). Qed.
Lemma lem7611487 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611488 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term223 A _97913 _97914 _97912) = (term224 A _97913 _97914 _97912).
Proof. exact (@lem7611487 (_97914 = _97913) (term184 _97914) (term225 A _97913 _97914 _97912)). Qed.
Lemma lem7611504 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611505 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term226 A _97913 _97914 _97912) = (term227 A _97913 _97914 _97912).
Proof. exact (@lem7611504 (term187 A _97914) (term184 _97914) (term222 A _97913 _97914 _97912)). Qed.
Lemma lem7611535 (_97914 : nat) (_97913 : nat) : (term228 _97914 _97913) = (term228 _97914 _97913).
Proof. exact (eq_refl (term228 _97914 _97913)). Qed.
Lemma lem7611536 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term224 A _97913 _97914 _97912) = (term229 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611535 _97914 _97913) (@lem7611505 A _97913 _97914 _97912)). Qed.
Lemma lem7611547 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term223 A _97913 _97914 _97912) = (term229 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611488 A _97913 _97914 _97912) (@lem7611536 A _97913 _97914 _97912)). Qed.
Lemma lem7611548 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term210 A _97912 _97914 _97913) = (term229 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611483 A _97913 _97914 _97912) (@lem7611547 A _97913 _97914 _97912)). Qed.
Lemma lem7611549 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term209 A _97912 _97914 _97913) = (term229 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611361 A _97912 _97914 _97913) (@lem7611548 A _97913 _97914 _97912)). Qed.
Lemma lem7611550 (_97913 : nat) : (term53 _97913) = (term53 _97913).
Proof. exact (eq_refl (term53 _97913)). Qed.
Lemma lem7611551 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term230 A _97912 _97914 _97913) = (term231 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611550 _97913) (@lem7611549 A _97913 _97914 _97912)). Qed.
Lemma lem7611555 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611556 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term231 A _97913 _97914 _97912) = (term232 A _97913 _97914 _97912).
Proof. exact (@lem7611555 (_97914 = _97913) (term184 _97913) (term227 A _97913 _97914 _97912)). Qed.
Lemma lem7611572 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611573 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term233 A _97913 _97914 _97912) = (term234 A _97913 _97914 _97912).
Proof. exact (@lem7611572 (term187 A _97914) (term184 _97913) (term235 A _97913 _97914 _97912)). Qed.
Lemma lem7611613 (_97914 : nat) (_97913 : nat) : (term228 _97914 _97913) = (term228 _97914 _97913).
Proof. exact (eq_refl (term228 _97914 _97913)). Qed.
Lemma lem7611614 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term232 A _97913 _97914 _97912) = (term236 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611613 _97914 _97913) (@lem7611573 A _97913 _97914 _97912)). Qed.
Lemma lem7611625 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term231 A _97913 _97914 _97912) = (term236 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611556 A _97913 _97914 _97912) (@lem7611614 A _97913 _97914 _97912)). Qed.
Lemma lem7611626 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term230 A _97912 _97914 _97913) = (term236 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611551 A _97913 _97914 _97912) (@lem7611625 A _97913 _97914 _97912)). Qed.
Lemma lem7611627 {A : Type'} (_97913 : nat) : (term219 A _97913) = (term219 A _97913).
Proof. exact (eq_refl (term219 A _97913)). Qed.
Lemma lem7611628 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term208 A _97912 _97914 _97913) = (term237 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611627 A _97913) (@lem7611626 A _97913 _97914 _97912)). Qed.
Lemma lem7611632 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611633 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term237 A _97913 _97914 _97912) = (term238 A _97913 _97914 _97912).
Proof. exact (@lem7611632 (_97914 = _97913) (term187 A _97913) (term234 A _97913 _97914 _97912)). Qed.
Lemma lem7611695 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term208 A _97912 _97914 _97913) = (term238 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611628 A _97913 _97914 _97912) (@lem7611633 A _97913 _97914 _97912)). Qed.
Lemma lem7611696 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term194 A _97912 _97914 _97913) = (term238 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611336 A _97912 _97914 _97913) (@lem7611695 A _97913 _97914 _97912)). Qed.
Lemma lem7611697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7611698 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term239 A _97912 _97914 _97913) = (term240 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611697) (@lem7611696 A _97913 _97914 _97912)). Qed.
Lemma lem7611714 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611715 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term241 A _97913 _97914 _97912) = (term242 A _97913 _97914 _97912).
Proof. exact (@lem7611714 (term187 A _97913) (term184 _97913) (term243 A _97913 _97914 _97912)). Qed.
Lemma lem7611739 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611740 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term243 A _97913 _97914 _97912) = (term244 A _97913 _97914 _97912).
Proof. exact (@lem7611739 (term184 _97914) (term188 A _97913 _97912) (term51 A _97914 _97912)). Qed.
Lemma lem7611754 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611755 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term245 A _97913 _97914 _97912) = (term225 A _97913 _97914 _97912).
Proof. exact (@lem7611754 (term187 A _97914) (term188 A _97913 _97912) (term188 A _97914 _97912)). Qed.
Lemma lem7611775 (_97914 : nat) : (term53 _97914) = (term53 _97914).
Proof. exact (eq_refl (term53 _97914)). Qed.
Lemma lem7611776 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term244 A _97913 _97914 _97912) = (term226 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611775 _97914) (@lem7611755 A _97913 _97914 _97912)). Qed.
Lemma lem7611780 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611781 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term226 A _97913 _97914 _97912) = (term227 A _97913 _97914 _97912).
Proof. exact (@lem7611780 (term187 A _97914) (term184 _97914) (term222 A _97913 _97914 _97912)). Qed.
Lemma lem7611811 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term244 A _97913 _97914 _97912) = (term227 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611776 A _97913 _97914 _97912) (@lem7611781 A _97913 _97914 _97912)). Qed.
Lemma lem7611812 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term243 A _97913 _97914 _97912) = (term227 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611740 A _97913 _97914 _97912) (@lem7611811 A _97913 _97914 _97912)). Qed.
Lemma lem7611813 (_97913 : nat) : (term53 _97913) = (term53 _97913).
Proof. exact (eq_refl (term53 _97913)). Qed.
Lemma lem7611814 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term246 A _97913 _97914 _97912) = (term233 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611813 _97913) (@lem7611812 A _97913 _97914 _97912)). Qed.
Lemma lem7611818 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7611819 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term233 A _97913 _97914 _97912) = (term234 A _97913 _97914 _97912).
Proof. exact (@lem7611818 (term187 A _97914) (term184 _97913) (term235 A _97913 _97914 _97912)). Qed.
Lemma lem7611859 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term246 A _97913 _97914 _97912) = (term234 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611814 A _97913 _97914 _97912) (@lem7611819 A _97913 _97914 _97912)). Qed.
Lemma lem7611860 {A : Type'} (_97913 : nat) : (term219 A _97913) = (term219 A _97913).
Proof. exact (eq_refl (term219 A _97913)). Qed.
Lemma lem7611861 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term242 A _97913 _97914 _97912) = (term247 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611860 A _97913) (@lem7611859 A _97913 _97914 _97912)). Qed.
Lemma lem7611872 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term241 A _97913 _97914 _97912) = (term247 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611715 A _97913 _97914 _97912) (@lem7611861 A _97913 _97914 _97912)). Qed.
Lemma lem7611873 (_97914 : nat) (_97913 : nat) : (term228 _97914 _97913) = (term228 _97914 _97913).
Proof. exact (eq_refl (term228 _97914 _97913)). Qed.
Lemma lem7611874 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term248 A _97913 _97914 _97912) = (term238 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611873 _97914 _97913) (@lem7611872 A _97913 _97914 _97912)). Qed.
Lemma lem7611885 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : ((term194 A _97912 _97914 _97913) = (term248 A _97913 _97914 _97912)) = ((term238 A _97913 _97914 _97912) = (term238 A _97913 _97914 _97912)).
Proof. exact (MK_COMB (@lem7611698 A _97913 _97914 _97912) (@lem7611874 A _97913 _97914 _97912)). Qed.
Lemma lem7611887 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7611888 (x : Prop) : (x = x) = True.
Proof. exact (@lem7611887 Prop x). Qed.
Lemma lem7611889 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : ((term238 A _97913 _97914 _97912) = (term238 A _97913 _97914 _97912)) = True.
Proof. exact (@lem7611888 (term238 A _97913 _97914 _97912)). Qed.
Lemma lem7611890 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : ((term194 A _97912 _97914 _97913) = (term248 A _97913 _97914 _97912)) = True.
Proof. exact (TRANS (@lem7611885 A _97913 _97914 _97912) (@lem7611889 A _97913 _97914 _97912)). Qed.
Lemma lem7611891 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : True = ((term194 A _97912 _97914 _97913) = (term248 A _97913 _97914 _97912)).
Proof. exact (SYM (@lem7611890 A _97913 _97914 _97912)). Qed.
Lemma lem7611892 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term194 A _97912 _97914 _97913) = (term248 A _97913 _97914 _97912).
Proof. exact (EQ_MP (@lem7611891 A _97913 _97914 _97912) (@lem0)). Qed.
Lemma lem7611893 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) (n : type34 A) (h1 : term171 A n) : term248 A _97913 _97914 _97912.
Proof. exact (EQ_MP (@lem7611892 A _97913 _97914 _97912) (@lem7611021 A _97912 _97914 _97913 n h1)). Qed.
Lemma lem7611895 (b : Prop) (a : Prop) : (a \/ b) = (term249 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7611896 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term248 A _97913 _97914 _97912) = (term250 A _97912 _97914 _97913).
Proof. exact (@lem7611895 (term241 A _97913 _97914 _97912) (_97914 = _97913)). Qed.
Lemma lem7611898 (a : Prop) (b : Prop) : (term251 a b) = (term252 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7611899 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term253 A _97913 _97914 _97912) = (term254 A _97913 _97914 _97912).
Proof. exact (@lem7611898 (term184 _97913) (term255 A _97913 _97914 _97912)). Qed.
Lemma lem7611901 (a : Prop) : (term256 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7611902 (_97913 : nat) : (term257 _97913) = (term57 _97913).
Proof. exact (@lem7611901 (term57 _97913)). Qed.
Lemma lem7611903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7611904 (_97913 : nat) : (term258 _97913) = (term259 _97913).
Proof. exact (MK_COMB (@lem7611903) (@lem7611902 _97913)). Qed.
Lemma lem7611906 (a : Prop) (b : Prop) : (term251 a b) = (term252 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7611907 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term260 A _97913 _97914 _97912) = (term261 A _97913 _97914 _97912).
Proof. exact (@lem7611906 (term187 A _97913) (term243 A _97913 _97914 _97912)). Qed.
Lemma lem7611909 (a : Prop) : (term256 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7611910 {A : Type'} (_97913 : nat) : (term262 A _97913) = (term52 A _97913).
Proof. exact (@lem7611909 (term52 A _97913)). Qed.
Lemma lem7611911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7611912 {A : Type'} (_97913 : nat) : (term263 A _97913) = (term264 A _97913).
Proof. exact (MK_COMB (@lem7611911) (@lem7611910 A _97913)). Qed.
Lemma lem7611914 (a : Prop) (b : Prop) : (term251 a b) = (term252 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7611915 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term265 A _97913 _97914 _97912) = (term266 A _97913 _97914 _97912).
Proof. exact (@lem7611914 (term188 A _97913 _97912) (term55 A _97914 _97912)). Qed.
Lemma lem7611917 (a : Prop) : (term256 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7611918 {A : Type'} (_97913 : nat) (_97912 : finite_image A) : (term267 A _97913 _97912) = ((@finite_index A _97913) = _97912).
Proof. exact (@lem7611917 ((@finite_index A _97913) = _97912)). Qed.
Lemma lem7611919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7611920 {A : Type'} (_97913 : nat) (_97912 : finite_image A) : (term268 A _97913 _97912) = (term269 A _97913 _97912).
Proof. exact (MK_COMB (@lem7611919) (@lem7611918 A _97913 _97912)). Qed.
Lemma lem7611922 (a : Prop) (b : Prop) : (term251 a b) = (term252 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7611923 {A : Type'} (_97914 : nat) (_97912 : finite_image A) : (term270 A _97914 _97912) = (term271 A _97914 _97912).
Proof. exact (@lem7611922 (term184 _97914) (term51 A _97914 _97912)). Qed.
Lemma lem7611925 (a : Prop) : (term256 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7611926 (_97914 : nat) : (term257 _97914) = (term57 _97914).
Proof. exact (@lem7611925 (term57 _97914)). Qed.
Lemma lem7611927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7611928 (_97914 : nat) : (term258 _97914) = (term259 _97914).
Proof. exact (MK_COMB (@lem7611927) (@lem7611926 _97914)). Qed.
Lemma lem7611930 (a : Prop) (b : Prop) : (term251 a b) = (term252 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7611931 {A : Type'} (_97914 : nat) (_97912 : finite_image A) : (term272 A _97914 _97912) = (term273 A _97914 _97912).
Proof. exact (@lem7611930 (term187 A _97914) (term188 A _97914 _97912)). Qed.
Lemma lem7611933 (a : Prop) : (term256 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7611934 {A : Type'} (_97914 : nat) : (term262 A _97914) = (term52 A _97914).
Proof. exact (@lem7611933 (term52 A _97914)). Qed.
Lemma lem7611935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7611936 {A : Type'} (_97914 : nat) : (term263 A _97914) = (term264 A _97914).
Proof. exact (MK_COMB (@lem7611935) (@lem7611934 A _97914)). Qed.
Lemma lem7611938 (a : Prop) : (term256 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7611939 {A : Type'} (_97914 : nat) (_97912 : finite_image A) : (term267 A _97914 _97912) = ((@finite_index A _97914) = _97912).
Proof. exact (@lem7611938 ((@finite_index A _97914) = _97912)). Qed.
Lemma lem7611940 {A : Type'} (_97914 : nat) (_97912 : finite_image A) : (term273 A _97914 _97912) = (term58 A _97914 _97912).
Proof. exact (MK_COMB (@lem7611936 A _97914) (@lem7611939 A _97914 _97912)). Qed.
Lemma lem7611941 {A : Type'} (_97914 : nat) (_97912 : finite_image A) : (term272 A _97914 _97912) = (term58 A _97914 _97912).
Proof. exact (TRANS (@lem7611931 A _97914 _97912) (@lem7611940 A _97914 _97912)). Qed.
Lemma lem7611942 {A : Type'} (_97914 : nat) (_97912 : finite_image A) : (term271 A _97914 _97912) = (term20 A _97914 _97912).
Proof. exact (MK_COMB (@lem7611928 _97914) (@lem7611941 A _97914 _97912)). Qed.
Lemma lem7611943 {A : Type'} (_97914 : nat) (_97912 : finite_image A) : (term270 A _97914 _97912) = (term20 A _97914 _97912).
Proof. exact (TRANS (@lem7611923 A _97914 _97912) (@lem7611942 A _97914 _97912)). Qed.
Lemma lem7611944 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term266 A _97913 _97914 _97912) = (term274 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611920 A _97913 _97912) (@lem7611943 A _97914 _97912)). Qed.
Lemma lem7611945 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term265 A _97913 _97914 _97912) = (term274 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611915 A _97913 _97914 _97912) (@lem7611944 A _97913 _97914 _97912)). Qed.
Lemma lem7611946 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term261 A _97913 _97914 _97912) = (term275 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611912 A _97913) (@lem7611945 A _97913 _97914 _97912)). Qed.
Lemma lem7611947 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term260 A _97913 _97914 _97912) = (term275 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611907 A _97913 _97914 _97912) (@lem7611946 A _97913 _97914 _97912)). Qed.
Lemma lem7611948 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term254 A _97913 _97914 _97912) = (term276 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611904 _97913) (@lem7611947 A _97913 _97914 _97912)). Qed.
Lemma lem7611949 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term253 A _97913 _97914 _97912) = (term276 A _97913 _97914 _97912).
Proof. exact (TRANS (@lem7611899 A _97913 _97914 _97912) (@lem7611948 A _97913 _97914 _97912)). Qed.
Lemma lem7611950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7611951 {A : Type'} (_97913 : nat) (_97914 : nat) (_97912 : finite_image A) : (term277 A _97913 _97914 _97912) = (term278 A _97913 _97914 _97912).
Proof. exact (MK_COMB (@lem7611950) (@lem7611949 A _97913 _97914 _97912)). Qed.
Lemma lem7611952 (_97914 : nat) (_97913 : nat) : (_97914 = _97913) = (_97914 = _97913).
Proof. exact (eq_refl (_97914 = _97913)). Qed.
Lemma lem7611953 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term250 A _97912 _97914 _97913) = (term279 A _97912 _97914 _97913).
Proof. exact (MK_COMB (@lem7611951 A _97913 _97914 _97912) (@lem7611952 _97914 _97913)). Qed.
Lemma lem7611954 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) : (term248 A _97913 _97914 _97912) = (term279 A _97912 _97914 _97913).
Proof. exact (TRANS (@lem7611896 A _97912 _97914 _97913) (@lem7611953 A _97912 _97914 _97913)). Qed.
Lemma lem7611956 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) (h2 : term177 A i j) : term280 A i j.
Proof. exact (conj (@lem7611322 A i j h1) (@lem7611329 A i j h2)). Qed.
Lemma lem7611957 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) (h2 : term177 A i j) : term281 A i j.
Proof. exact (conj (@lem7611315 A i j h1) (@lem7611956 A i j h1 h2)). Qed.
Lemma lem7611958 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) (h2 : term177 A i j) : term282 A i j.
Proof. exact (conj (@lem7611308 A j) (@lem7611957 A i j h1 h2)). Qed.
Lemma lem7611959 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) (h2 : term177 A i j) : term283 A i j.
Proof. exact (conj (@lem7611299 A i j h1) (@lem7611958 A i j h1 h2)). Qed.
Lemma lem7611960 {A : Type'} (i : nat) (j : nat) (h1 : term32 A i j) (h2 : term177 A i j) : term284 A i j.
Proof. exact (conj (@lem7611292 A i j h1) (@lem7611959 A i j h1 h2)). Qed.
Lemma lem7611962 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) (n : type34 A) (h1 : term171 A n) : term279 A _97912 _97914 _97913.
Proof. exact (EQ_MP (@lem7611954 A _97912 _97914 _97913) (@lem7611893 A _97913 _97914 _97912 n h1)). Qed.
Lemma lem7611963 {A : Type'} (_97912 : finite_image A) (_97914 : nat) (_97913 : nat) (n : type34 A) (h1 : term171 A n) : term279 A _97912 _97914 _97913.
Proof. exact (@lem7611962 A _97912 _97914 _97913 n h1). Qed.
Lemma lem7611964 {A : Type'} (i : nat) (j : nat) (n : type34 A) (h1 : term171 A n) : term285 A i j.
Proof. exact (@lem7611963 A (@finite_index A j) i j n h1). Qed.
Lemma lem7611967 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) (h3 : term177 A i j) : i = j.
Proof. exact (@lem7611964 A i j n h1 (@lem7611960 A i j h2 h3)). Qed.
Lemma lem7611968 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) (h3 : term177 A i j) : term286 i j.
Proof. exact (fun h0 : term195 i j => @lem7611967 A n i j h1 h2 h3). Qed.
Lemma lem7611970 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7611971 (i : nat) (j : nat) : (term286 i j) = (i = j).
Proof. exact (@lem7611970 (i = j)). Qed.
Lemma lem7611972 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) (h3 : term177 A i j) : i = j.
Proof. exact (EQ_MP (@lem7611971 i j) (@lem7611968 A n i j h1 h2 h3)). Qed.
Lemma lem7611975 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7611977 (i : nat) (j : nat) : (term195 i j) = (term287 i j).
Proof. exact (@lem7611975 (i = j)). Qed.
Lemma lem7611980 {A : Type'} (i : nat) (j : nat) (h1 : term177 A i j) : term287 i j.
Proof. exact (EQ_MP (@lem7611977 i j) (@lem7611025 A i j h1)). Qed.
Lemma lem7611983 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) (h3 : term177 A i j) : False.
Proof. exact (@lem7611980 A i j h3 (@lem7611972 A n i j h1 h2 h3)). Qed.
Lemma lem7611984 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) (h3 : term177 A i j) : term288.
Proof. exact (fun h0 : ~ False => @lem7611983 A n i j h1 h2 h3). Qed.
Lemma lem7611986 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7611987 : term288 = False.
Proof. exact (@lem7611986 False). Qed.
Lemma lem7611988 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) (h3 : term177 A i j) : False.
Proof. exact (EQ_MP (@lem7611987) (@lem7611984 A n i j h1 h2 h3)). Qed.
Lemma lem7612055 {A : Type'} (x : finite_image A) : x = x.
Proof. exact (@lem21386 (finite_image A) x). Qed.
Lemma lem7612056 {A : Type'} (x : finite_image A) : x = x.
Proof. exact (@lem7612055 A x). Qed.
Lemma lem7612057 {A : Type'} (j : nat) : (@finite_index A j) = (@finite_index A j).
Proof. exact (@lem7612056 A (@finite_index A j)). Qed.
Lemma lem7612058 {A : Type'} (j : nat) : term206 A j.
Proof. exact (fun h0 : term200 A j => @lem7612057 A j). Qed.
Lemma lem7612060 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7612061 {A : Type'} (j : nat) : (term206 A j) = ((@finite_index A j) = (@finite_index A j)).
Proof. exact (@lem7612060 ((@finite_index A j) = (@finite_index A j))). Qed.
Lemma lem7612062 {A : Type'} (j : nat) : (@finite_index A j) = (@finite_index A j).
Proof. exact (EQ_MP (@lem7612061 A j) (@lem7612058 A j)). Qed.
Lemma lem7612065 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7612067 {A : Type'} (j : nat) : (term200 A j) = (term289 A j).
Proof. exact (@lem7612065 ((@finite_index A j) = (@finite_index A j))). Qed.
Lemma lem7612070 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : term289 A j.
Proof. exact (EQ_MP (@lem7612067 A j) (@lem7611178 A i j h1)). Qed.
Lemma lem7612073 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : False.
Proof. exact (@lem7612070 A i j h1 (@lem7612062 A j)). Qed.
Lemma lem7612074 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : term288.
Proof. exact (fun h0 : ~ False => @lem7612073 A i j h1). Qed.
Lemma lem7612076 (p : Prop) : (term204 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7612077 : term288 = False.
Proof. exact (@lem7612076 False). Qed.
Lemma lem7612079 {A : Type'} (i : nat) (j : nat) (h1 : term178 A i j) : False.
Proof. exact (EQ_MP (@lem7612077) (@lem7612074 A i j h1)). Qed.
Lemma lem7612080 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) : False.
Proof. exact (or_elim (@lem7610706 A i j h2) (fun h0 : term177 A i j => @lem7611988 A n i j h1 h2 h0) (fun h0 : term178 A i j => @lem7612079 A i j h0)). Qed.
Lemma lem7612081 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) : (term32 A i j) = False.
Proof. exact (prop_ext (fun h3 : term32 A i j => @lem7612080 A n i j h1 h2) (fun h3 : False => @lem7610705 A i j h2)). Qed.
Lemma lem7612082 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) : False.
Proof. exact (EQ_MP (@lem7612081 A n i j h1 h2) (@lem7610705 A i j h2)). Qed.
Lemma lem7612083 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) : (term171 A n) = False.
Proof. exact (prop_ext (fun h3 : term171 A n => @lem7612082 A n i j h1 h2) (fun h3 : False => @lem7610619 A n h1)). Qed.
Lemma lem7612084 {A : Type'} (n : type34 A) (i : nat) (j : nat) (h1 : term171 A n) (h2 : term32 A i j) : False.
Proof. exact (EQ_MP (@lem7612083 A n i j h1 h2) (@lem7610619 A n h1)). Qed.
Lemma lem7612085 {A : Type'} (i : nat) (n : type34 A) (h1 : term43 A i) (h2 : term171 A n) : False.
Proof. exact (ex_elim (@lem7610486 A i h1) (fun j : nat => fun h0 : term42 A i j => @lem7612084 A n i j h2 h0)). Qed.
Lemma lem7612086 {A : Type'} (n : type34 A) (h1 : term10 A) (h2 : term171 A n) : False.
Proof. exact (ex_elim (@lem7610148 A h1) (fun i : nat => fun h0 : term48 A i => @lem7612085 A i n h0 h2)). Qed.
Lemma lem7612087 {A : Type'} (h1 : term17 A) (h2 : term10 A) : False.
Proof. exact (ex_elim (@lem7610484 A h1) (fun n : type34 A => fun h0 : term173 A n => @lem7612086 A n h2 h0)). Qed.
Lemma lem7612088 {A : Type'} (h1 : term10 A) : term15 A.
Proof. exact (fun h0 : term17 A => @lem7612087 A h0 h1). Qed.
Lemma lem7612089 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (@lem69 (term17 A)). Qed.
Lemma lem7612090 {A : Type'} (h1 : term10 A) : term16 A.
Proof. exact (EQ_MP (@lem7612089 A) (@lem7612088 A h1)). Qed.
Lemma lem7612091 {A : Type'} : term19 A.
Proof. exact (fun h0 : term10 A => @lem7612090 A h0). Qed.
Lemma lem7612092 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem7610036 A) (@lem7612091 A)). Qed.
Lemma lem7612094 {A : Type'} : term11 A.
Proof. exact (@lem7609914 A (@lem7612092 A)). Qed.
Lemma lem7612095 {A : Type'} (h1 : term10 A) : term15 A.
Proof. exact (@lem7612094 A (@lem7609894 A h1)). Qed.
Lemma lem7612096 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem7612095 A h1 (@lem7609879 A)). Qed.
Lemma lem7612097 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem7612096 A h1) (fun h2 : False => @lem7609894 A h1)). Qed.
Lemma lem7612098 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem7612097 A h1) (@lem7609894 A h1)). Qed.
Lemma lem7612099 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem7612098 A h0). Qed.
Lemma lem7612100 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem7609893 A) (@lem7612099 A)). Qed.
