Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_RELATED_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import ITERATE_RELATED_spec.
Require Import MONOIDAL_ADD_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import nsum_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Require Import thm7_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7030907 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7030908 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7030909 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7030908 t1) (@lem7030907 t1)). Qed.
Lemma lem7030910 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7030909 t1 t2). Qed.
Lemma lem7030911 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7030912 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7030911 t1 t2) (@lem7030910 t1 t2)). Qed.
Lemma lem7030913 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7030912 t1 t2 t3). Qed.
Lemma lem7030914 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7030915 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7030914 t1 t2 t3) (@lem7030913 t1 t2 t3)). Qed.
Lemma lem7030916 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7030915 t1 t2 t3)). Qed.
Lemma lem7030917 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (h1). Qed.
Lemma lem7030918 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (SYM (@lem7030917 _126417 h1)). Qed.
Lemma lem7030919 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (h1). Qed.
Lemma lem7030920 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (SYM (@lem7030919 _126417 h1)). Qed.
Lemma lem7030921 {_126417 : Type'} : ((@nsum _126417) = (@iterate nat _126417 Nat.add)) = ((@iterate nat _126417 Nat.add) = (@nsum _126417)).
Proof. exact (prop_ext (fun h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add) => @lem7030918 _126417 h1) (fun h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417) => @lem7030920 _126417 h1)). Qed.
Lemma lem7030923 {A B : Type'} (op : type1400 B) : term7 A B op.
Proof. exact (@lem5783455 A B op). Qed.
Lemma lem7030924 {A B : Type'} (op : type1400 B) : (term7 A B op) = (term8 A B op).
Proof. exact (eq_refl (term7 A B op)). Qed.
Lemma lem7030927 {A B : Type'} (op : type1400 B) : term8 A B op.
Proof. exact (EQ_MP (@lem7030924 A B op) (@lem7030923 A B op)). Qed.
Lemma lem7030928 {A : Type'} (op : type1606) : term9 A op.
Proof. exact (@lem7030927 A nat op). Qed.
Lemma lem7030929 {A : Type'} : term10 A.
Proof. exact (@lem7030928 A Nat.add). Qed.
Lemma lem7030930 {A : Type'} : term11 A.
Proof. exact (@lem7030929 A (@lem6924403)). Qed.
Lemma lem7030931 {A : Type'} (R : type1605) : term12 A R.
Proof. exact (@lem7030930 A R). Qed.
Lemma lem7030932 {A : Type'} (R : type1605) : (term12 A R) = (term13 A R).
Proof. exact (eq_refl (term12 A R)). Qed.
Lemma lem7030933 {A : Type'} (R : type1605) : term13 A R.
Proof. exact (EQ_MP (@lem7030932 A R) (@lem7030931 A R)). Qed.
Lemma lem7030934 {A : Type'} (P : Prop) : term14 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem7030935 {A : Type'} (P : Prop) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem7030936 {A : Type'} (P : Prop) : term15 A P.
Proof. exact (EQ_MP (@lem7030935 A P) (@lem7030934 A P)). Qed.
Lemma lem7030937 {A : Type'} (P : Prop) (Q : A -> Prop) : term16 A P Q.
Proof. exact (@lem7030936 A P Q). Qed.
Lemma lem7030938 {A : Type'} (P : Prop) (Q : A -> Prop) : (term16 A P Q) = ((term17 A P Q) = (term18 A P Q)).
Proof. exact (eq_refl (term16 A P Q)). Qed.
Lemma lem7030977 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7030978 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term21 A R f s g) = (term22 A R f s g).
Proof. exact (@lem7030977 (term23 R) (term24 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7030982 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7030983 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term26 A R f s g) = (term27 A R f s g).
Proof. exact (@lem7030982 (term28 R) (term29 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7031023 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7031024 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term30 R m m' n n') = (term31 R m m' n n').
Proof. exact (@lem7031023 (R m n) (R m' n') (term32 R m m' n n')). Qed.
Lemma lem7031029 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term33 R m m' n) = (term34 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7031024 R m m' n n')). Qed.
Lemma lem7031030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7031031 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term35 R m m' n) = (term36 R m m' n).
Proof. exact (MK_COMB (@lem7031030) (@lem7031029 R m m' n)). Qed.
Lemma lem7031033 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7030938 A P Q) (@lem7030937 A P Q)). Qed.
Lemma lem7031034 (P : Prop) (Q : nat -> Prop) : (term37 P Q) = (term38 P Q).
Proof. exact (@lem7031033 nat P Q). Qed.
Lemma lem7031035 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term39 R m m' n) = (term40 R m m' n).
Proof. exact (@lem7031034 (R m n) (term41 R m m' n)). Qed.
Lemma lem7031036 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term42 R m m' n n') = (term43 R m m' n n').
Proof. exact (eq_refl (term42 R m m' n n')). Qed.
Lemma lem7031037 (R : type1605) (m : nat) (n : nat) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7031038 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term45 R m m' n n') = (term31 R m m' n n').
Proof. exact (MK_COMB (@lem7031037 R m n) (@lem7031036 R m m' n n')). Qed.
Lemma lem7031039 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term46 R m m' n) = (term34 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7031038 R m m' n n')). Qed.
Lemma lem7031040 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7031041 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term39 R m m' n) = (term36 R m m' n).
Proof. exact (MK_COMB (@lem7031040) (@lem7031039 R m m' n)). Qed.
Lemma lem7031042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7031043 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term47 R m m' n) = (term48 R m m' n).
Proof. exact (MK_COMB (@lem7031042) (@lem7031041 R m m' n)). Qed.
Lemma lem7031044 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term42 R m m' n n') = (term43 R m m' n n').
Proof. exact (eq_refl (term42 R m m' n n')). Qed.
Lemma lem7031045 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term49 R m m' n) = (term41 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7031044 R m m' n n')). Qed.
Lemma lem7031046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7031047 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term50 R m m' n) = (term51 R m m' n).
Proof. exact (MK_COMB (@lem7031046) (@lem7031045 R m m' n)). Qed.
Lemma lem7031048 (R : type1605) (m : nat) (n : nat) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7031049 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term40 R m m' n) = (term52 R m m' n).
Proof. exact (MK_COMB (@lem7031048 R m n) (@lem7031047 R m m' n)). Qed.
Lemma lem7031050 (R : type1605) (m : nat) (m' : nat) (n : nat) : ((term39 R m m' n) = (term40 R m m' n)) = ((term36 R m m' n) = (term52 R m m' n)).
Proof. exact (MK_COMB (@lem7031043 R m m' n) (@lem7031049 R m m' n)). Qed.
Lemma lem7031051 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term36 R m m' n) = (term52 R m m' n).
Proof. exact (EQ_MP (@lem7031050 R m m' n) (@lem7031035 R m m' n)). Qed.
Lemma lem7031080 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term35 R m m' n) = (term52 R m m' n).
Proof. exact (TRANS (@lem7031031 R m m' n) (@lem7031051 R m m' n)). Qed.
Lemma lem7031081 (R : type1605) (m : nat) (n : nat) : (term53 R m n) = (term54 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7031080 R m m' n)). Qed.
Lemma lem7031082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7031083 (R : type1605) (m : nat) (n : nat) : (term55 R m n) = (term56 R m n).
Proof. exact (MK_COMB (@lem7031082) (@lem7031081 R m n)). Qed.
Lemma lem7031085 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7030938 A P Q) (@lem7030937 A P Q)). Qed.
Lemma lem7031086 (P : Prop) (Q : nat -> Prop) : (term37 P Q) = (term38 P Q).
Proof. exact (@lem7031085 nat P Q). Qed.
Lemma lem7031087 (R : type1605) (m : nat) (n : nat) : (term57 R m n) = (term58 R m n).
Proof. exact (@lem7031086 (R m n) (term59 R m n)). Qed.
Lemma lem7031088 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term60 R m n m') = (term51 R m m' n).
Proof. exact (eq_refl (term60 R m n m')). Qed.
Lemma lem7031089 (R : type1605) (m : nat) (n : nat) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7031090 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term61 R m n m') = (term52 R m m' n).
Proof. exact (MK_COMB (@lem7031089 R m n) (@lem7031088 R m m' n)). Qed.
Lemma lem7031091 (R : type1605) (m : nat) (n : nat) : (term62 R m n) = (term54 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7031090 R m m' n)). Qed.
Lemma lem7031092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7031093 (R : type1605) (m : nat) (n : nat) : (term57 R m n) = (term56 R m n).
Proof. exact (MK_COMB (@lem7031092) (@lem7031091 R m n)). Qed.
Lemma lem7031094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7031095 (R : type1605) (m : nat) (n : nat) : (term63 R m n) = (term64 R m n).
Proof. exact (MK_COMB (@lem7031094) (@lem7031093 R m n)). Qed.
Lemma lem7031096 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term60 R m n m') = (term51 R m m' n).
Proof. exact (eq_refl (term60 R m n m')). Qed.
Lemma lem7031097 (R : type1605) (m : nat) (n : nat) : (term65 R m n) = (term59 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7031096 R m m' n)). Qed.
Lemma lem7031098 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7031099 (R : type1605) (m : nat) (n : nat) : (term66 R m n) = (term67 R m n).
Proof. exact (MK_COMB (@lem7031098) (@lem7031097 R m n)). Qed.
Lemma lem7031100 (R : type1605) (m : nat) (n : nat) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7031101 (R : type1605) (m : nat) (n : nat) : (term58 R m n) = (term68 R m n).
Proof. exact (MK_COMB (@lem7031100 R m n) (@lem7031099 R m n)). Qed.
Lemma lem7031102 (R : type1605) (m : nat) (n : nat) : ((term57 R m n) = (term58 R m n)) = ((term56 R m n) = (term68 R m n)).
Proof. exact (MK_COMB (@lem7031095 R m n) (@lem7031101 R m n)). Qed.
Lemma lem7031103 (R : type1605) (m : nat) (n : nat) : (term56 R m n) = (term68 R m n).
Proof. exact (EQ_MP (@lem7031102 R m n) (@lem7031087 R m n)). Qed.
Lemma lem7031136 (R : type1605) (m : nat) (n : nat) : (term55 R m n) = (term68 R m n).
Proof. exact (TRANS (@lem7031083 R m n) (@lem7031103 R m n)). Qed.
Lemma lem7031137 (R : type1605) (m : nat) : (term69 R m) = (term70 R m).
Proof. exact (fun_ext (fun n : nat => @lem7031136 R m n)). Qed.
Lemma lem7031138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7031139 (R : type1605) (m : nat) : (term71 R m) = (term72 R m).
Proof. exact (MK_COMB (@lem7031138) (@lem7031137 R m)). Qed.
Lemma lem7031164 (R : type1605) : (term73 R) = (term74 R).
Proof. exact (fun_ext (fun m : nat => @lem7031139 R m)). Qed.
Lemma lem7031165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7031166 (R : type1605) : (term28 R) = (term75 R).
Proof. exact (MK_COMB (@lem7031165) (@lem7031164 R)). Qed.
Lemma lem7031171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7031172 (R : type1605) : (term76 R) = (term77 R).
Proof. exact (MK_COMB (@lem7031171) (@lem7031166 R)). Qed.
Lemma lem7031174 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7031175 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term78 A R f s g) = (term79 A R f s g).
Proof. exact (@lem7031174 (@FINITE A s) (term80 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7031206 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term27 A R f s g) = (term81 A R f s g).
Proof. exact (MK_COMB (@lem7031172 R) (@lem7031175 A R f s g)). Qed.
Lemma lem7031209 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term26 A R f s g) = (term81 A R f s g).
Proof. exact (TRANS (@lem7030983 A R f s g) (@lem7031206 A R f s g)). Qed.
Lemma lem7031210 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031211 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term22 A R f s g) = (term83 A R f s g).
Proof. exact (MK_COMB (@lem7031210 R) (@lem7031209 A R f s g)). Qed.
Lemma lem7031214 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term21 A R f s g) = (term83 A R f s g).
Proof. exact (TRANS (@lem7030978 A R f s g) (@lem7031211 A R f s g)). Qed.
Lemma lem7031215 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term84 A R f g) = (term85 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7031214 A R f s g)). Qed.
Lemma lem7031216 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7031217 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term86 A R f g) = (term87 A R f g).
Proof. exact (MK_COMB (@lem7031216 A) (@lem7031215 A R f g)). Qed.
Lemma lem7031219 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7030938 A P Q) (@lem7030937 A P Q)). Qed.
Lemma lem7031220 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem7031219 (A -> Prop) P Q). Qed.
Lemma lem7031221 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term90 A R f g) = (term91 A R f g).
Proof. exact (@lem7031220 A (term23 R) (term92 A R f g)). Qed.
Lemma lem7031222 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term93 A R f g s) = (term81 A R f s g).
Proof. exact (eq_refl (term93 A R f g s)). Qed.
Lemma lem7031223 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031224 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term94 A R f g s) = (term83 A R f s g).
Proof. exact (MK_COMB (@lem7031223 R) (@lem7031222 A R f s g)). Qed.
Lemma lem7031225 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term95 A R f g) = (term85 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7031224 A R f s g)). Qed.
Lemma lem7031226 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7031227 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term90 A R f g) = (term87 A R f g).
Proof. exact (MK_COMB (@lem7031226 A) (@lem7031225 A R f g)). Qed.
Lemma lem7031228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7031229 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term96 A R f g) = (term97 A R f g).
Proof. exact (MK_COMB (@lem7031228) (@lem7031227 A R f g)). Qed.
Lemma lem7031230 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term93 A R f g s) = (term81 A R f s g).
Proof. exact (eq_refl (term93 A R f g s)). Qed.
Lemma lem7031231 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term98 A R f g) = (term92 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7031230 A R f s g)). Qed.
Lemma lem7031232 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7031233 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term99 A R f g) = (term100 A R f g).
Proof. exact (MK_COMB (@lem7031232 A) (@lem7031231 A R f g)). Qed.
Lemma lem7031234 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031235 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term91 A R f g) = (term101 A R f g).
Proof. exact (MK_COMB (@lem7031234 R) (@lem7031233 A R f g)). Qed.
Lemma lem7031236 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : ((term90 A R f g) = (term91 A R f g)) = ((term87 A R f g) = (term101 A R f g)).
Proof. exact (MK_COMB (@lem7031229 A R f g) (@lem7031235 A R f g)). Qed.
Lemma lem7031237 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term87 A R f g) = (term101 A R f g).
Proof. exact (EQ_MP (@lem7031236 A R f g) (@lem7031221 A R f g)). Qed.
Lemma lem7031241 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7030938 A P Q) (@lem7030937 A P Q)). Qed.
Lemma lem7031242 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem7031241 (A -> Prop) P Q). Qed.
Lemma lem7031243 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term102 A R f g) = (term103 A R f g).
Proof. exact (@lem7031242 A (term75 R) (term104 A R f g)). Qed.
Lemma lem7031244 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term105 A R f g s) = (term79 A R f s g).
Proof. exact (eq_refl (term105 A R f g s)). Qed.
Lemma lem7031245 (R : type1605) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7031246 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term106 A R f g s) = (term81 A R f s g).
Proof. exact (MK_COMB (@lem7031245 R) (@lem7031244 A R f s g)). Qed.
Lemma lem7031247 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term107 A R f g) = (term92 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7031246 A R f s g)). Qed.
Lemma lem7031248 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7031249 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term102 A R f g) = (term100 A R f g).
Proof. exact (MK_COMB (@lem7031248 A) (@lem7031247 A R f g)). Qed.
Lemma lem7031250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7031251 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term108 A R f g) = (term109 A R f g).
Proof. exact (MK_COMB (@lem7031250) (@lem7031249 A R f g)). Qed.
Lemma lem7031252 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term105 A R f g s) = (term79 A R f s g).
Proof. exact (eq_refl (term105 A R f g s)). Qed.
Lemma lem7031253 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term110 A R f g) = (term104 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7031252 A R f s g)). Qed.
Lemma lem7031254 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7031255 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term111 A R f g) = (term112 A R f g).
Proof. exact (MK_COMB (@lem7031254 A) (@lem7031253 A R f g)). Qed.
Lemma lem7031256 (R : type1605) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7031257 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term103 A R f g) = (term113 A R f g).
Proof. exact (MK_COMB (@lem7031256 R) (@lem7031255 A R f g)). Qed.
Lemma lem7031258 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : ((term102 A R f g) = (term103 A R f g)) = ((term100 A R f g) = (term113 A R f g)).
Proof. exact (MK_COMB (@lem7031251 A R f g) (@lem7031257 A R f g)). Qed.
Lemma lem7031259 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term100 A R f g) = (term113 A R f g).
Proof. exact (EQ_MP (@lem7031258 A R f g) (@lem7031243 A R f g)). Qed.
Lemma lem7031376 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031377 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term101 A R f g) = (term114 A R f g).
Proof. exact (MK_COMB (@lem7031376 R) (@lem7031259 A R f g)). Qed.
Lemma lem7031380 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term87 A R f g) = (term114 A R f g).
Proof. exact (TRANS (@lem7031237 A R f g) (@lem7031377 A R f g)). Qed.
Lemma lem7031381 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term86 A R f g) = (term114 A R f g).
Proof. exact (TRANS (@lem7031217 A R f g) (@lem7031380 A R f g)). Qed.
Lemma lem7031382 {A : Type'} (R : type1605) (f : A -> nat) : (term115 A R f) = (term116 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7031381 A R f g)). Qed.
Lemma lem7031383 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031384 {A : Type'} (R : type1605) (f : A -> nat) : (term117 A R f) = (term118 A R f).
Proof. exact (MK_COMB (@lem7031383 A) (@lem7031382 A R f)). Qed.
Lemma lem7031386 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7030938 A P Q) (@lem7030937 A P Q)). Qed.
Lemma lem7031387 {A : Type'} (P : Prop) (Q : type704 A) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem7031386 (A -> nat) P Q). Qed.
Lemma lem7031388 {A : Type'} (R : type1605) (f : A -> nat) : (term121 A R f) = (term122 A R f).
Proof. exact (@lem7031387 A (term23 R) (term123 A R f)). Qed.
Lemma lem7031389 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term124 A R f g) = (term113 A R f g).
Proof. exact (eq_refl (term124 A R f g)). Qed.
Lemma lem7031390 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031391 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term125 A R f g) = (term114 A R f g).
Proof. exact (MK_COMB (@lem7031390 R) (@lem7031389 A R f g)). Qed.
Lemma lem7031392 {A : Type'} (R : type1605) (f : A -> nat) : (term126 A R f) = (term116 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7031391 A R f g)). Qed.
Lemma lem7031393 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031394 {A : Type'} (R : type1605) (f : A -> nat) : (term121 A R f) = (term118 A R f).
Proof. exact (MK_COMB (@lem7031393 A) (@lem7031392 A R f)). Qed.
Lemma lem7031395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7031396 {A : Type'} (R : type1605) (f : A -> nat) : (term127 A R f) = (term128 A R f).
Proof. exact (MK_COMB (@lem7031395) (@lem7031394 A R f)). Qed.
Lemma lem7031397 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term124 A R f g) = (term113 A R f g).
Proof. exact (eq_refl (term124 A R f g)). Qed.
Lemma lem7031398 {A : Type'} (R : type1605) (f : A -> nat) : (term129 A R f) = (term123 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7031397 A R f g)). Qed.
Lemma lem7031399 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031400 {A : Type'} (R : type1605) (f : A -> nat) : (term130 A R f) = (term131 A R f).
Proof. exact (MK_COMB (@lem7031399 A) (@lem7031398 A R f)). Qed.
Lemma lem7031401 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031402 {A : Type'} (R : type1605) (f : A -> nat) : (term122 A R f) = (term132 A R f).
Proof. exact (MK_COMB (@lem7031401 R) (@lem7031400 A R f)). Qed.
Lemma lem7031403 {A : Type'} (R : type1605) (f : A -> nat) : ((term121 A R f) = (term122 A R f)) = ((term118 A R f) = (term132 A R f)).
Proof. exact (MK_COMB (@lem7031396 A R f) (@lem7031402 A R f)). Qed.
Lemma lem7031404 {A : Type'} (R : type1605) (f : A -> nat) : (term118 A R f) = (term132 A R f).
Proof. exact (EQ_MP (@lem7031403 A R f) (@lem7031388 A R f)). Qed.
Lemma lem7031408 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7030938 A P Q) (@lem7030937 A P Q)). Qed.
Lemma lem7031409 {A : Type'} (P : Prop) (Q : type704 A) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem7031408 (A -> nat) P Q). Qed.
Lemma lem7031410 {A : Type'} (R : type1605) (f : A -> nat) : (term133 A R f) = (term134 A R f).
Proof. exact (@lem7031409 A (term75 R) (term135 A R f)). Qed.
Lemma lem7031411 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term136 A R f g) = (term112 A R f g).
Proof. exact (eq_refl (term136 A R f g)). Qed.
Lemma lem7031412 (R : type1605) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7031413 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term137 A R f g) = (term113 A R f g).
Proof. exact (MK_COMB (@lem7031412 R) (@lem7031411 A R f g)). Qed.
Lemma lem7031414 {A : Type'} (R : type1605) (f : A -> nat) : (term138 A R f) = (term123 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7031413 A R f g)). Qed.
Lemma lem7031415 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031416 {A : Type'} (R : type1605) (f : A -> nat) : (term133 A R f) = (term131 A R f).
Proof. exact (MK_COMB (@lem7031415 A) (@lem7031414 A R f)). Qed.
Lemma lem7031417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7031418 {A : Type'} (R : type1605) (f : A -> nat) : (term139 A R f) = (term140 A R f).
Proof. exact (MK_COMB (@lem7031417) (@lem7031416 A R f)). Qed.
Lemma lem7031419 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term136 A R f g) = (term112 A R f g).
Proof. exact (eq_refl (term136 A R f g)). Qed.
Lemma lem7031420 {A : Type'} (R : type1605) (f : A -> nat) : (term141 A R f) = (term135 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7031419 A R f g)). Qed.
Lemma lem7031421 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031422 {A : Type'} (R : type1605) (f : A -> nat) : (term142 A R f) = (term143 A R f).
Proof. exact (MK_COMB (@lem7031421 A) (@lem7031420 A R f)). Qed.
Lemma lem7031423 (R : type1605) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7031424 {A : Type'} (R : type1605) (f : A -> nat) : (term134 A R f) = (term144 A R f).
Proof. exact (MK_COMB (@lem7031423 R) (@lem7031422 A R f)). Qed.
Lemma lem7031425 {A : Type'} (R : type1605) (f : A -> nat) : ((term133 A R f) = (term134 A R f)) = ((term131 A R f) = (term144 A R f)).
Proof. exact (MK_COMB (@lem7031418 A R f) (@lem7031424 A R f)). Qed.
Lemma lem7031426 {A : Type'} (R : type1605) (f : A -> nat) : (term131 A R f) = (term144 A R f).
Proof. exact (EQ_MP (@lem7031425 A R f) (@lem7031410 A R f)). Qed.
Lemma lem7031547 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031548 {A : Type'} (R : type1605) (f : A -> nat) : (term132 A R f) = (term145 A R f).
Proof. exact (MK_COMB (@lem7031547 R) (@lem7031426 A R f)). Qed.
Lemma lem7031551 {A : Type'} (R : type1605) (f : A -> nat) : (term118 A R f) = (term145 A R f).
Proof. exact (TRANS (@lem7031404 A R f) (@lem7031548 A R f)). Qed.
Lemma lem7031552 {A : Type'} (R : type1605) (f : A -> nat) : (term117 A R f) = (term145 A R f).
Proof. exact (TRANS (@lem7031384 A R f) (@lem7031551 A R f)). Qed.
Lemma lem7031553 {A : Type'} (R : type1605) : (term146 A R) = (term147 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7031552 A R f)). Qed.
Lemma lem7031554 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031555 {A : Type'} (R : type1605) : (term148 A R) = (term149 A R).
Proof. exact (MK_COMB (@lem7031554 A) (@lem7031553 A R)). Qed.
Lemma lem7031557 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7030938 A P Q) (@lem7030937 A P Q)). Qed.
Lemma lem7031558 {A : Type'} (P : Prop) (Q : type704 A) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem7031557 (A -> nat) P Q). Qed.
Lemma lem7031559 {A : Type'} (R : type1605) : (term150 A R) = (term151 A R).
Proof. exact (@lem7031558 A (term23 R) (term152 A R)). Qed.
Lemma lem7031560 {A : Type'} (R : type1605) (f : A -> nat) : (term153 A R f) = (term144 A R f).
Proof. exact (eq_refl (term153 A R f)). Qed.
Lemma lem7031561 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031562 {A : Type'} (R : type1605) (f : A -> nat) : (term154 A R f) = (term145 A R f).
Proof. exact (MK_COMB (@lem7031561 R) (@lem7031560 A R f)). Qed.
Lemma lem7031563 {A : Type'} (R : type1605) : (term155 A R) = (term147 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7031562 A R f)). Qed.
Lemma lem7031564 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031565 {A : Type'} (R : type1605) : (term150 A R) = (term149 A R).
Proof. exact (MK_COMB (@lem7031564 A) (@lem7031563 A R)). Qed.
Lemma lem7031566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7031567 {A : Type'} (R : type1605) : (term156 A R) = (term157 A R).
Proof. exact (MK_COMB (@lem7031566) (@lem7031565 A R)). Qed.
Lemma lem7031568 {A : Type'} (R : type1605) (f : A -> nat) : (term153 A R f) = (term144 A R f).
Proof. exact (eq_refl (term153 A R f)). Qed.
Lemma lem7031569 {A : Type'} (R : type1605) : (term158 A R) = (term152 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7031568 A R f)). Qed.
Lemma lem7031570 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031571 {A : Type'} (R : type1605) : (term159 A R) = (term160 A R).
Proof. exact (MK_COMB (@lem7031570 A) (@lem7031569 A R)). Qed.
Lemma lem7031572 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031573 {A : Type'} (R : type1605) : (term151 A R) = (term161 A R).
Proof. exact (MK_COMB (@lem7031572 R) (@lem7031571 A R)). Qed.
Lemma lem7031574 {A : Type'} (R : type1605) : ((term150 A R) = (term151 A R)) = ((term149 A R) = (term161 A R)).
Proof. exact (MK_COMB (@lem7031567 A R) (@lem7031573 A R)). Qed.
Lemma lem7031575 {A : Type'} (R : type1605) : (term149 A R) = (term161 A R).
Proof. exact (EQ_MP (@lem7031574 A R) (@lem7031559 A R)). Qed.
Lemma lem7031579 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7030938 A P Q) (@lem7030937 A P Q)). Qed.
Lemma lem7031580 {A : Type'} (P : Prop) (Q : type704 A) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem7031579 (A -> nat) P Q). Qed.
Lemma lem7031581 {A : Type'} (R : type1605) : (term162 A R) = (term163 A R).
Proof. exact (@lem7031580 A (term75 R) (term164 A R)). Qed.
Lemma lem7031582 {A : Type'} (R : type1605) (f : A -> nat) : (term165 A R f) = (term143 A R f).
Proof. exact (eq_refl (term165 A R f)). Qed.
Lemma lem7031583 (R : type1605) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7031584 {A : Type'} (R : type1605) (f : A -> nat) : (term166 A R f) = (term144 A R f).
Proof. exact (MK_COMB (@lem7031583 R) (@lem7031582 A R f)). Qed.
Lemma lem7031585 {A : Type'} (R : type1605) : (term167 A R) = (term152 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7031584 A R f)). Qed.
Lemma lem7031586 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031587 {A : Type'} (R : type1605) : (term162 A R) = (term160 A R).
Proof. exact (MK_COMB (@lem7031586 A) (@lem7031585 A R)). Qed.
Lemma lem7031588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7031589 {A : Type'} (R : type1605) : (term168 A R) = (term169 A R).
Proof. exact (MK_COMB (@lem7031588) (@lem7031587 A R)). Qed.
Lemma lem7031590 {A : Type'} (R : type1605) (f : A -> nat) : (term165 A R f) = (term143 A R f).
Proof. exact (eq_refl (term165 A R f)). Qed.
Lemma lem7031591 {A : Type'} (R : type1605) : (term170 A R) = (term164 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7031590 A R f)). Qed.
Lemma lem7031592 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031593 {A : Type'} (R : type1605) : (term171 A R) = (term172 A R).
Proof. exact (MK_COMB (@lem7031592 A) (@lem7031591 A R)). Qed.
Lemma lem7031594 (R : type1605) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7031595 {A : Type'} (R : type1605) : (term163 A R) = (term173 A R).
Proof. exact (MK_COMB (@lem7031594 R) (@lem7031593 A R)). Qed.
Lemma lem7031596 {A : Type'} (R : type1605) : ((term162 A R) = (term163 A R)) = ((term160 A R) = (term173 A R)).
Proof. exact (MK_COMB (@lem7031589 A R) (@lem7031595 A R)). Qed.
Lemma lem7031597 {A : Type'} (R : type1605) : (term160 A R) = (term173 A R).
Proof. exact (EQ_MP (@lem7031596 A R) (@lem7031581 A R)). Qed.
Lemma lem7031722 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7031723 {A : Type'} (R : type1605) : (term161 A R) = (term174 A R).
Proof. exact (MK_COMB (@lem7031722 R) (@lem7031597 A R)). Qed.
Lemma lem7031726 {A : Type'} (R : type1605) : (term149 A R) = (term174 A R).
Proof. exact (TRANS (@lem7031575 A R) (@lem7031723 A R)). Qed.
Lemma lem7031727 {A : Type'} (R : type1605) : (term148 A R) = (term174 A R).
Proof. exact (TRANS (@lem7031555 A R) (@lem7031726 A R)). Qed.
Lemma lem7031728 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (fun_ext (fun R : type1605 => @lem7031727 A R)). Qed.
Lemma lem7031729 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem7031730 {A : Type'} : (term177 A) = (term178 A).
Proof. exact (MK_COMB (@lem7031729) (@lem7031728 A)). Qed.
Lemma lem7031755 {A : Type'} : (term178 A) = (term177 A).
Proof. exact (SYM (@lem7031730 A)). Qed.
Lemma lem7031756 (R : type1605) (h1 : term23 R) : term23 R.
Proof. exact (h1). Qed.
Lemma lem7031757 (R : type1605) (h1 : term75 R) : term75 R.
Proof. exact (h1). Qed.
Lemma lem7031758 (R : type1605) : (term23 R) = ((term23 R) = True).
Proof. exact (@lem7 (term23 R)). Qed.
Lemma lem7031775 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7031776 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7031777 (R : type1605) : (term179 R) = (term180 R).
Proof. exact (MK_COMB (@lem7031776 R) (@lem7031775)). Qed.
Lemma lem7031779 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7031780 (R : type1605) : (term181 R) = (term23 R).
Proof. exact (MK_COMB (@lem7031777 R) (@lem7031779)). Qed.
Lemma lem7031782 (R : type1605) (h1 : term23 R) : (term23 R) = True.
Proof. exact (EQ_MP (@lem7031758 R) (@lem7031756 R h1)). Qed.
Lemma lem7031783 (R : type1605) (h1 : term23 R) : (term181 R) = True.
Proof. exact (TRANS (@lem7031780 R) (@lem7031782 R h1)). Qed.
Lemma lem7031784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7031785 (R : type1605) (h1 : term23 R) : (term182 R) = (and True).
Proof. exact (MK_COMB (@lem7031784) (@lem7031783 R h1)). Qed.
Lemma lem7031806 (R : type1605) : (term183 R) = (term183 R).
Proof. exact (eq_refl (term183 R)). Qed.
Lemma lem7031807 (R : type1605) (h1 : term23 R) : (term184 R) = (term185 R).
Proof. exact (MK_COMB (@lem7031785 R h1) (@lem7031806 R)). Qed.
Lemma lem7031809 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7031810 (R : type1605) : (term185 R) = (term183 R).
Proof. exact (@lem7031809 (term183 R)). Qed.
Lemma lem7031831 (R : type1605) (h1 : term23 R) : (term184 R) = (term183 R).
Proof. exact (TRANS (@lem7031807 R h1) (@lem7031810 R)). Qed.
Lemma lem7031832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7031833 (R : type1605) (h1 : term23 R) : (term186 R) = (term187 R).
Proof. exact (MK_COMB (@lem7031832) (@lem7031831 R h1)). Qed.
Lemma lem7031857 {_126417 : Type'} : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (EQ_MP (@lem7030921 _126417) (@lem6920372 _126417)). Qed.
Lemma lem7031858 {A : Type'} : (@iterate nat A Nat.add) = (@nsum A).
Proof. exact (@lem7031857 A). Qed.
Lemma lem7031859 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7031860 {A : Type'} (s : A -> Prop) : (@iterate nat A Nat.add s) = (@nsum A s).
Proof. exact (MK_COMB (@lem7031858 A) (@lem7031859 A s)). Qed.
Lemma lem7031861 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7031862 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@iterate nat A Nat.add s f) = (@nsum A s f).
Proof. exact (MK_COMB (@lem7031860 A s) (@lem7031861 A f)). Qed.
Lemma lem7031863 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7031864 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term188 A R s f) = (term189 A R s f).
Proof. exact (MK_COMB (@lem7031863 R) (@lem7031862 A s f)). Qed.
Lemma lem7031866 {_126417 : Type'} : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (EQ_MP (@lem7030921 _126417) (@lem6920372 _126417)). Qed.
Lemma lem7031867 {A : Type'} : (@iterate nat A Nat.add) = (@nsum A).
Proof. exact (@lem7031866 A). Qed.
Lemma lem7031868 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7031869 {A : Type'} (s : A -> Prop) : (@iterate nat A Nat.add s) = (@nsum A s).
Proof. exact (MK_COMB (@lem7031867 A) (@lem7031868 A s)). Qed.
Lemma lem7031870 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7031871 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@iterate nat A Nat.add s g) = (@nsum A s g).
Proof. exact (MK_COMB (@lem7031869 A s) (@lem7031870 A g)). Qed.
Lemma lem7031872 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term190 A R f s g) = (term25 A R f s g).
Proof. exact (MK_COMB (@lem7031864 A R s f) (@lem7031871 A s g)). Qed.
Lemma lem7031873 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term191 A s R f g) = (term191 A s R f g).
Proof. exact (eq_refl (term191 A s R f g)). Qed.
Lemma lem7031874 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term192 A R f s g) = (term78 A R f s g).
Proof. exact (MK_COMB (@lem7031873 A s R f g) (@lem7031872 A R f s g)). Qed.
Lemma lem7031877 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term193 A R f g) = (term194 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7031874 A R f s g)). Qed.
Lemma lem7031878 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7031879 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term195 A R f g) = (term196 A R f g).
Proof. exact (MK_COMB (@lem7031878 A) (@lem7031877 A R f g)). Qed.
Lemma lem7031884 {A : Type'} (R : type1605) (f : A -> nat) : (term197 A R f) = (term198 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7031879 A R f g)). Qed.
Lemma lem7031885 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031886 {A : Type'} (R : type1605) (f : A -> nat) : (term199 A R f) = (term200 A R f).
Proof. exact (MK_COMB (@lem7031885 A) (@lem7031884 A R f)). Qed.
Lemma lem7031891 {A : Type'} (R : type1605) : (term201 A R) = (term202 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7031886 A R f)). Qed.
Lemma lem7031892 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7031893 {A : Type'} (R : type1605) : (term203 A R) = (term204 A R).
Proof. exact (MK_COMB (@lem7031892 A) (@lem7031891 A R)). Qed.
Lemma lem7031898 {A : Type'} (R : type1605) (h1 : term23 R) : (term13 A R) = (term205 A R).
Proof. exact (MK_COMB (@lem7031833 R h1) (@lem7031893 A R)). Qed.
Lemma lem7031901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7031902 {A : Type'} (R : type1605) (h1 : term23 R) : (term206 A R) = (term207 A R).
Proof. exact (MK_COMB (@lem7031901) (@lem7031898 A R h1)). Qed.
Lemma lem7031925 {A : Type'} (R : type1605) : (term172 A R) = (term172 A R).
Proof. exact (eq_refl (term172 A R)). Qed.
Lemma lem7031926 {A : Type'} (R : type1605) (h1 : term23 R) : (term208 A R) = (term209 A R).
Proof. exact (MK_COMB (@lem7031902 A R h1) (@lem7031925 A R)). Qed.
Lemma lem7031929 {A : Type'} (R : type1605) (h1 : term23 R) : (term209 A R) = (term208 A R).
Proof. exact (SYM (@lem7031926 A R h1)). Qed.
Lemma lem7031931 (p : Prop) : p = (term210 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7031932 {A : Type'} (R : type1605) : (term209 A R) = (term211 A R).
Proof. exact (@lem7031931 (term209 A R)). Qed.
Lemma lem7031933 {A : Type'} (R : type1605) : (term211 A R) = (term209 A R).
Proof. exact (SYM (@lem7031932 A R)). Qed.
Lemma lem7031934 {A : Type'} (R : type1605) (h1 : term212 A R) : term212 A R.
Proof. exact (h1). Qed.
Lemma lem7031937 {A : Type'} (R : type1605) (h1 : term213 A R) : term213 A R.
Proof. exact (h1). Qed.
Lemma lem7031938 {A : Type'} (R : type1605) : term214 A R.
Proof. exact (fun h0 : term213 A R => @lem7031937 A R h0). Qed.
Lemma lem7031939 {A : Type'} (R : type1605) (h1 : term214 A R) : term214 A R.
Proof. exact (h1). Qed.
Lemma lem7031940 {A : Type'} (R : type1605) (h1 : term213 A R) : term213 A R.
Proof. exact (h1). Qed.
Lemma lem7031941 {A : Type'} (R : type1605) (h1 : term214 A R) (h2 : term213 A R) : term213 A R.
Proof. exact (@lem7031939 A R h1 (@lem7031940 A R h2)). Qed.
Lemma lem7031942 {A : Type'} (R : type1605) (h1 : term213 A R) : term215 A R.
Proof. exact (fun h0 : term214 A R => @lem7031941 A R h0 h1). Qed.
Lemma lem7031943 {A : Type'} (R : type1605) (h1 : term214 A R) : term214 A R.
Proof. exact (h1). Qed.
Lemma lem7031944 {A : Type'} (R : type1605) (h1 : term214 A R) (h2 : term213 A R) : term213 A R.
Proof. exact (@lem7031942 A R h2 (@lem7031943 A R h1)). Qed.
Lemma lem7031945 {A : Type'} (R : type1605) (h1 : term214 A R) : term214 A R.
Proof. exact (fun h0 : term213 A R => @lem7031944 A R h1 h0). Qed.
Lemma lem7031946 {A : Type'} (R : type1605) : term216 A R.
Proof. exact (fun h0 : term214 A R => @lem7031945 A R h0). Qed.
Lemma lem7031949 {A : Type'} (R : type1605) : term214 A R.
Proof. exact (@lem7031946 A R (@lem7031938 A R)). Qed.
Lemma lem7031950 {A : Type'} (R : type1605) : term214 A R.
Proof. exact (@lem7031949 A R). Qed.
Lemma lem7031980 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7031981 {A : Type'} (R : type1605) : (term211 A R) = (term217 A R).
Proof. exact (@lem7031980 (term212 A R)). Qed.
Lemma lem7031983 (t : Prop) : (term218 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7031984 {A : Type'} (R : type1605) : (term217 A R) = (term209 A R).
Proof. exact (@lem7031983 (term209 A R)). Qed.
Lemma lem7031987 {A : Type'} (R : type1605) : (term211 A R) = (term209 A R).
Proof. exact (TRANS (@lem7031981 A R) (@lem7031984 A R)). Qed.
Lemma lem7032054 (R : type1605) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7032055 {A : Type'} (R : type1605) : (term219 A R) = (term220 A R).
Proof. exact (MK_COMB (@lem7032054 R) (@lem7031987 A R)). Qed.
Lemma lem7032058 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7032059 {A : Type'} (R : type1605) : (term213 A R) = (term221 A R).
Proof. exact (MK_COMB (@lem7032058 R) (@lem7032055 A R)). Qed.
Lemma lem7032062 {A : Type'} : (term222 A) = (term223 A).
Proof. exact (fun_ext (fun R : type1605 => @lem7032059 A R)). Qed.
Lemma lem7032063 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem7032072 {A : Type'} : (term224 A) = (term225 A).
Proof. exact (MK_COMB (@lem7032063) (@lem7032062 A)). Qed.
Lemma lem7032073 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7032078 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term226 A s R f g x) = (term226 A s R f g x).
Proof. exact (eq_refl (term226 A s R f g x)). Qed.
Lemma lem7032079 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term227 A s R f g) = (term227 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7032078 A s R f g x)). Qed.
Lemma lem7032080 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7032081 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term80 A s R f g) = (term80 A s R f g).
Proof. exact (MK_COMB (@lem7032080 A) (@lem7032079 A s R f g)). Qed.
Lemma lem7032082 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7032083 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term228 A s R f g) = (term228 A s R f g).
Proof. exact (MK_COMB (@lem7032082) (@lem7032081 A s R f g)). Qed.
Lemma lem7032084 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term229 A R f s g) = (term229 A R f s g).
Proof. exact (MK_COMB (@lem7032083 A s R f g) (@lem7032073 A R f s g)). Qed.
Lemma lem7032087 {A : Type'} (s : A -> Prop) : (term230 A s) = (term230 A s).
Proof. exact (eq_refl (term230 A s)). Qed.
Lemma lem7032088 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term79 A R f s g) = (term79 A R f s g).
Proof. exact (MK_COMB (@lem7032087 A s) (@lem7032084 A R f s g)). Qed.
Lemma lem7032089 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term104 A R f g) = (term104 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7032088 A R f s g)). Qed.
Lemma lem7032090 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7032091 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term112 A R f g) = (term112 A R f g).
Proof. exact (MK_COMB (@lem7032090 A) (@lem7032089 A R f g)). Qed.
Lemma lem7032092 {A : Type'} (R : type1605) (f : A -> nat) : (term135 A R f) = (term135 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7032091 A R f g)). Qed.
Lemma lem7032093 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032094 {A : Type'} (R : type1605) (f : A -> nat) : (term143 A R f) = (term143 A R f).
Proof. exact (MK_COMB (@lem7032093 A) (@lem7032092 A R f)). Qed.
Lemma lem7032095 {A : Type'} (R : type1605) : (term164 A R) = (term164 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7032094 A R f)). Qed.
Lemma lem7032096 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032097 {A : Type'} (R : type1605) : (term172 A R) = (term172 A R).
Proof. exact (MK_COMB (@lem7032096 A) (@lem7032095 A R)). Qed.
Lemma lem7032098 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7032103 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term226 A s R f g x) = (term226 A s R f g x).
Proof. exact (eq_refl (term226 A s R f g x)). Qed.
Lemma lem7032104 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term227 A s R f g) = (term227 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7032103 A s R f g x)). Qed.
Lemma lem7032105 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7032106 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term80 A s R f g) = (term80 A s R f g).
Proof. exact (MK_COMB (@lem7032105 A) (@lem7032104 A s R f g)). Qed.
Lemma lem7032109 {A : Type'} (s : A -> Prop) : (term231 A s) = (term231 A s).
Proof. exact (eq_refl (term231 A s)). Qed.
Lemma lem7032110 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term29 A s R f g) = (term29 A s R f g).
Proof. exact (MK_COMB (@lem7032109 A s) (@lem7032106 A s R f g)). Qed.
Lemma lem7032111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7032112 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term191 A s R f g) = (term191 A s R f g).
Proof. exact (MK_COMB (@lem7032111) (@lem7032110 A s R f g)). Qed.
Lemma lem7032113 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term78 A R f s g) = (term78 A R f s g).
Proof. exact (MK_COMB (@lem7032112 A s R f g) (@lem7032098 A R f s g)). Qed.
Lemma lem7032114 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term194 A R f g) = (term194 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7032113 A R f s g)). Qed.
Lemma lem7032115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7032116 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term196 A R f g) = (term196 A R f g).
Proof. exact (MK_COMB (@lem7032115 A) (@lem7032114 A R f g)). Qed.
Lemma lem7032117 {A : Type'} (R : type1605) (f : A -> nat) : (term198 A R f) = (term198 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7032116 A R f g)). Qed.
Lemma lem7032118 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032119 {A : Type'} (R : type1605) (f : A -> nat) : (term200 A R f) = (term200 A R f).
Proof. exact (MK_COMB (@lem7032118 A) (@lem7032117 A R f)). Qed.
Lemma lem7032120 {A : Type'} (R : type1605) : (term202 A R) = (term202 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7032119 A R f)). Qed.
Lemma lem7032121 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032122 {A : Type'} (R : type1605) : (term204 A R) = (term204 A R).
Proof. exact (MK_COMB (@lem7032121 A) (@lem7032120 A R)). Qed.
Lemma lem7032131 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term30 R x1 y1 x2 y2) = (term30 R x1 y1 x2 y2).
Proof. exact (eq_refl (term30 R x1 y1 x2 y2)). Qed.
Lemma lem7032132 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term33 R x1 y1 x2) = (term33 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : nat => @lem7032131 R x1 y1 x2 y2)). Qed.
Lemma lem7032133 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032134 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term35 R x1 y1 x2) = (term35 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7032133) (@lem7032132 R x1 y1 x2)). Qed.
Lemma lem7032135 (R : type1605) (x1 : nat) (y1 : nat) : (term232 R x1 y1) = (term232 R x1 y1).
Proof. exact (fun_ext (fun x2 : nat => @lem7032134 R x1 y1 x2)). Qed.
Lemma lem7032136 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032137 (R : type1605) (x1 : nat) (y1 : nat) : (term233 R x1 y1) = (term233 R x1 y1).
Proof. exact (MK_COMB (@lem7032136) (@lem7032135 R x1 y1)). Qed.
Lemma lem7032138 (R : type1605) (x1 : nat) : (term234 R x1) = (term234 R x1).
Proof. exact (fun_ext (fun y1 : nat => @lem7032137 R x1 y1)). Qed.
Lemma lem7032139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032140 (R : type1605) (x1 : nat) : (term235 R x1) = (term235 R x1).
Proof. exact (MK_COMB (@lem7032139) (@lem7032138 R x1)). Qed.
Lemma lem7032141 (R : type1605) : (term236 R) = (term236 R).
Proof. exact (fun_ext (fun x1 : nat => @lem7032140 R x1)). Qed.
Lemma lem7032142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032143 (R : type1605) : (term183 R) = (term183 R).
Proof. exact (MK_COMB (@lem7032142) (@lem7032141 R)). Qed.
Lemma lem7032144 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7032145 (R : type1605) : (term187 R) = (term187 R).
Proof. exact (MK_COMB (@lem7032144) (@lem7032143 R)). Qed.
Lemma lem7032146 {A : Type'} (R : type1605) : (term205 A R) = (term205 A R).
Proof. exact (MK_COMB (@lem7032145 R) (@lem7032122 A R)). Qed.
Lemma lem7032147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7032148 {A : Type'} (R : type1605) : (term207 A R) = (term207 A R).
Proof. exact (MK_COMB (@lem7032147) (@lem7032146 A R)). Qed.
Lemma lem7032149 {A : Type'} (R : type1605) : (term209 A R) = (term209 A R).
Proof. exact (MK_COMB (@lem7032148 A R) (@lem7032097 A R)). Qed.
Lemma lem7032154 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term43 R m m' n n') = (term43 R m m' n n').
Proof. exact (eq_refl (term43 R m m' n n')). Qed.
Lemma lem7032155 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term41 R m m' n) = (term41 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7032154 R m m' n n')). Qed.
Lemma lem7032156 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032157 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term51 R m m' n) = (term51 R m m' n).
Proof. exact (MK_COMB (@lem7032156) (@lem7032155 R m m' n)). Qed.
Lemma lem7032158 (R : type1605) (m : nat) (n : nat) : (term59 R m n) = (term59 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7032157 R m m' n)). Qed.
Lemma lem7032159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032160 (R : type1605) (m : nat) (n : nat) : (term67 R m n) = (term67 R m n).
Proof. exact (MK_COMB (@lem7032159) (@lem7032158 R m n)). Qed.
Lemma lem7032163 (R : type1605) (m : nat) (n : nat) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7032164 (R : type1605) (m : nat) (n : nat) : (term68 R m n) = (term68 R m n).
Proof. exact (MK_COMB (@lem7032163 R m n) (@lem7032160 R m n)). Qed.
Lemma lem7032165 (R : type1605) (m : nat) : (term70 R m) = (term70 R m).
Proof. exact (fun_ext (fun n : nat => @lem7032164 R m n)). Qed.
Lemma lem7032166 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032167 (R : type1605) (m : nat) : (term72 R m) = (term72 R m).
Proof. exact (MK_COMB (@lem7032166) (@lem7032165 R m)). Qed.
Lemma lem7032168 (R : type1605) : (term74 R) = (term74 R).
Proof. exact (fun_ext (fun m : nat => @lem7032167 R m)). Qed.
Lemma lem7032169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032170 (R : type1605) : (term75 R) = (term75 R).
Proof. exact (MK_COMB (@lem7032169) (@lem7032168 R)). Qed.
Lemma lem7032171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7032172 (R : type1605) : (term77 R) = (term77 R).
Proof. exact (MK_COMB (@lem7032171) (@lem7032170 R)). Qed.
Lemma lem7032173 {A : Type'} (R : type1605) : (term220 A R) = (term220 A R).
Proof. exact (MK_COMB (@lem7032172 R) (@lem7032149 A R)). Qed.
Lemma lem7032176 (R : type1605) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7032177 {A : Type'} (R : type1605) : (term221 A R) = (term221 A R).
Proof. exact (MK_COMB (@lem7032176 R) (@lem7032173 A R)). Qed.
Lemma lem7032178 {A : Type'} : (term223 A) = (term223 A).
Proof. exact (fun_ext (fun R : type1605 => @lem7032177 A R)). Qed.
Lemma lem7032179 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem7032180 {A : Type'} : (term225 A) = (term225 A).
Proof. exact (MK_COMB (@lem7032179) (@lem7032178 A)). Qed.
Lemma lem7032313 {A : Type'} : (term224 A) = (term225 A).
Proof. exact (TRANS (@lem7032072 A) (@lem7032180 A)). Qed.
Lemma lem7032314 {A : Type'} : (term225 A) = (term224 A).
Proof. exact (SYM (@lem7032313 A)). Qed.
Lemma lem7032316 (R : type1605) (h1 : term75 R) : term75 R.
Proof. exact (h1). Qed.
Lemma lem7032317 {A : Type'} (R : type1605) (h1 : term205 A R) : term205 A R.
Proof. exact (h1). Qed.
Lemma lem7032319 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term80 A s R f g.
Proof. exact (h1). Qed.
Lemma lem7032321 (p : Prop) : p = (term210 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7032322 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term237 A R f s g).
Proof. exact (@lem7032321 (term25 A R f s g)). Qed.
Lemma lem7032323 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term237 A R f s g) = (term25 A R f s g).
Proof. exact (SYM (@lem7032322 A R f s g)). Qed.
Lemma lem7032324 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term238 A R f s g) : term238 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7032338 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term43 R m m' n n') = (term239 R m m' n n').
Proof. exact (@lem17265 (R m' n') (term32 R m m' n n')). Qed.
Lemma lem7032339 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term41 R m m' n) = (term240 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7032338 R m m' n n')). Qed.
Lemma lem7032340 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032341 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term51 R m m' n) = (term241 R m m' n).
Proof. exact (MK_COMB (@lem7032340) (@lem7032339 R m m' n)). Qed.
Lemma lem7032342 (R : type1605) (m : nat) (n : nat) : (term59 R m n) = (term242 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7032341 R m m' n)). Qed.
Lemma lem7032343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032344 (R : type1605) (m : nat) (n : nat) : (term67 R m n) = (term243 R m n).
Proof. exact (MK_COMB (@lem7032343) (@lem7032342 R m n)). Qed.
Lemma lem7032346 (R : type1605) (m : nat) (n : nat) : (term244 R m n) = (term244 R m n).
Proof. exact (eq_refl (term244 R m n)). Qed.
Lemma lem7032347 (R : type1605) (m : nat) (n : nat) : (term245 R m n) = (term246 R m n).
Proof. exact (MK_COMB (@lem7032346 R m n) (@lem7032344 R m n)). Qed.
Lemma lem7032348 (R : type1605) (m : nat) (n : nat) : (term68 R m n) = (term245 R m n).
Proof. exact (@lem17265 (R m n) (term67 R m n)). Qed.
Lemma lem7032349 (R : type1605) (m : nat) (n : nat) : (term68 R m n) = (term246 R m n).
Proof. exact (TRANS (@lem7032348 R m n) (@lem7032347 R m n)). Qed.
Lemma lem7032350 (R : type1605) (m : nat) : (term70 R m) = (term247 R m).
Proof. exact (fun_ext (fun n : nat => @lem7032349 R m n)). Qed.
Lemma lem7032351 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032352 (R : type1605) (m : nat) : (term72 R m) = (term248 R m).
Proof. exact (MK_COMB (@lem7032351) (@lem7032350 R m)). Qed.
Lemma lem7032353 (R : type1605) : (term74 R) = (term249 R).
Proof. exact (fun_ext (fun m : nat => @lem7032352 R m)). Qed.
Lemma lem7032354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7032463 (R : type1605) : (term75 R) = (term250 R).
Proof. exact (MK_COMB (@lem7032354) (@lem7032353 R)). Qed.
Lemma lem7032464 (R : type1605) (h1 : term75 R) : term250 R.
Proof. exact (EQ_MP (@lem7032463 R) (@lem7032316 R h1)). Qed.
Lemma lem7032475 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term251 R x1 y1 x2 y2) = (term252 R x1 y1 x2 y2).
Proof. exact (@lem17362 (term253 x1 x2 R y1 y2) (term32 R x1 y1 x2 y2)). Qed.
Lemma lem7032476 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7032477 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term256 R x1 y1 x2) = (term257 R x1 y1 x2).
Proof. exact (@lem7032476 (term33 R x1 y1 x2)). Qed.
Lemma lem7032478 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term258 R x1 y1 x2 y2) = (term30 R x1 y1 x2 y2).
Proof. exact (eq_refl (term258 R x1 y1 x2 y2)). Qed.
Lemma lem7032479 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7032480 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term259 R x1 y1 x2 y2) = (term251 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7032479) (@lem7032478 R x1 y1 x2 y2)). Qed.
Lemma lem7032481 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term259 R x1 y1 x2 y2) = (term252 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7032480 R x1 y1 x2 y2) (@lem7032475 R x1 y1 x2 y2)). Qed.
Lemma lem7032482 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term260 R x1 y1 x2) = (term261 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : nat => @lem7032481 R x1 y1 x2 y2)). Qed.
Lemma lem7032483 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032484 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term257 R x1 y1 x2) = (term262 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7032483) (@lem7032482 R x1 y1 x2)). Qed.
Lemma lem7032485 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term256 R x1 y1 x2) = (term262 R x1 y1 x2).
Proof. exact (TRANS (@lem7032477 R x1 y1 x2) (@lem7032484 R x1 y1 x2)). Qed.
Lemma lem7032486 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7032487 (R : type1605) (x1 : nat) (y1 : nat) : (term263 R x1 y1) = (term264 R x1 y1).
Proof. exact (@lem7032486 (term232 R x1 y1)). Qed.
Lemma lem7032488 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term265 R x1 y1 x2) = (term35 R x1 y1 x2).
Proof. exact (eq_refl (term265 R x1 y1 x2)). Qed.
Lemma lem7032489 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7032490 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term266 R x1 y1 x2) = (term256 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7032489) (@lem7032488 R x1 y1 x2)). Qed.
Lemma lem7032491 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term266 R x1 y1 x2) = (term262 R x1 y1 x2).
Proof. exact (TRANS (@lem7032490 R x1 y1 x2) (@lem7032485 R x1 y1 x2)). Qed.
Lemma lem7032492 (R : type1605) (x1 : nat) (y1 : nat) : (term267 R x1 y1) = (term268 R x1 y1).
Proof. exact (fun_ext (fun x2 : nat => @lem7032491 R x1 y1 x2)). Qed.
Lemma lem7032493 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032494 (R : type1605) (x1 : nat) (y1 : nat) : (term264 R x1 y1) = (term269 R x1 y1).
Proof. exact (MK_COMB (@lem7032493) (@lem7032492 R x1 y1)). Qed.
Lemma lem7032495 (R : type1605) (x1 : nat) (y1 : nat) : (term263 R x1 y1) = (term269 R x1 y1).
Proof. exact (TRANS (@lem7032487 R x1 y1) (@lem7032494 R x1 y1)). Qed.
Lemma lem7032496 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7032497 (R : type1605) (x1 : nat) : (term270 R x1) = (term271 R x1).
Proof. exact (@lem7032496 (term234 R x1)). Qed.
Lemma lem7032498 (R : type1605) (x1 : nat) (y1 : nat) : (term272 R x1 y1) = (term233 R x1 y1).
Proof. exact (eq_refl (term272 R x1 y1)). Qed.
Lemma lem7032499 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7032500 (R : type1605) (x1 : nat) (y1 : nat) : (term273 R x1 y1) = (term263 R x1 y1).
Proof. exact (MK_COMB (@lem7032499) (@lem7032498 R x1 y1)). Qed.
Lemma lem7032501 (R : type1605) (x1 : nat) (y1 : nat) : (term273 R x1 y1) = (term269 R x1 y1).
Proof. exact (TRANS (@lem7032500 R x1 y1) (@lem7032495 R x1 y1)). Qed.
Lemma lem7032502 (R : type1605) (x1 : nat) : (term274 R x1) = (term275 R x1).
Proof. exact (fun_ext (fun y1 : nat => @lem7032501 R x1 y1)). Qed.
Lemma lem7032503 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032504 (R : type1605) (x1 : nat) : (term271 R x1) = (term276 R x1).
Proof. exact (MK_COMB (@lem7032503) (@lem7032502 R x1)). Qed.
Lemma lem7032505 (R : type1605) (x1 : nat) : (term270 R x1) = (term276 R x1).
Proof. exact (TRANS (@lem7032497 R x1) (@lem7032504 R x1)). Qed.
Lemma lem7032506 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7032507 (R : type1605) : (term277 R) = (term278 R).
Proof. exact (@lem7032506 (term236 R)). Qed.
Lemma lem7032508 (R : type1605) (x1 : nat) : (term279 R x1) = (term235 R x1).
Proof. exact (eq_refl (term279 R x1)). Qed.
Lemma lem7032509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7032510 (R : type1605) (x1 : nat) : (term280 R x1) = (term270 R x1).
Proof. exact (MK_COMB (@lem7032509) (@lem7032508 R x1)). Qed.
Lemma lem7032511 (R : type1605) (x1 : nat) : (term280 R x1) = (term276 R x1).
Proof. exact (TRANS (@lem7032510 R x1) (@lem7032505 R x1)). Qed.
Lemma lem7032512 (R : type1605) : (term281 R) = (term282 R).
Proof. exact (fun_ext (fun x1 : nat => @lem7032511 R x1)). Qed.
Lemma lem7032513 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032514 (R : type1605) : (term278 R) = (term283 R).
Proof. exact (MK_COMB (@lem7032513) (@lem7032512 R)). Qed.
Lemma lem7032515 (R : type1605) : (term277 R) = (term283 R).
Proof. exact (TRANS (@lem7032507 R) (@lem7032514 R)). Qed.
Lemma lem7032523 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term284 A s R f g x) = (term285 A s R f g x).
Proof. exact (@lem17362 (@IN A x s) (term286 A R f g x)). Qed.
Lemma lem7032524 {A : Type'} (P : A -> Prop) : (term287 A P) = (term288 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7032525 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term289 A s R f g) = (term290 A s R f g).
Proof. exact (@lem7032524 A (term227 A s R f g)). Qed.
Lemma lem7032526 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term291 A s R f g x) = (term226 A s R f g x).
Proof. exact (eq_refl (term291 A s R f g x)). Qed.
Lemma lem7032527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7032528 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term292 A s R f g x) = (term284 A s R f g x).
Proof. exact (MK_COMB (@lem7032527) (@lem7032526 A s R f g x)). Qed.
Lemma lem7032529 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term292 A s R f g x) = (term285 A s R f g x).
Proof. exact (TRANS (@lem7032528 A s R f g x) (@lem7032523 A s R f g x)). Qed.
Lemma lem7032530 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term293 A s R f g) = (term294 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7032529 A s R f g x)). Qed.
Lemma lem7032531 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7032532 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term290 A s R f g) = (term295 A s R f g).
Proof. exact (MK_COMB (@lem7032531 A) (@lem7032530 A s R f g)). Qed.
Lemma lem7032533 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term289 A s R f g) = (term295 A s R f g).
Proof. exact (TRANS (@lem7032525 A s R f g) (@lem7032532 A s R f g)). Qed.
Lemma lem7032535 {A : Type'} (s : A -> Prop) : (term296 A s) = (term296 A s).
Proof. exact (eq_refl (term296 A s)). Qed.
Lemma lem7032536 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term297 A s R f g) = (term298 A s R f g).
Proof. exact (MK_COMB (@lem7032535 A s) (@lem7032533 A s R f g)). Qed.
Lemma lem7032537 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term299 A s R f g) = (term297 A s R f g).
Proof. exact (@lem17045 (@FINITE A s) (term80 A s R f g)). Qed.
Lemma lem7032538 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term299 A s R f g) = (term298 A s R f g).
Proof. exact (TRANS (@lem7032537 A s R f g) (@lem7032536 A s R f g)). Qed.
Lemma lem7032539 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7032540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032541 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term300 A s R f g) = (term301 A s R f g).
Proof. exact (MK_COMB (@lem7032540) (@lem7032538 A s R f g)). Qed.
Lemma lem7032542 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term302 A R f s g) = (term303 A R f s g).
Proof. exact (MK_COMB (@lem7032541 A s R f g) (@lem7032539 A R f s g)). Qed.
Lemma lem7032543 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term78 A R f s g) = (term302 A R f s g).
Proof. exact (@lem17265 (term29 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7032544 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term78 A R f s g) = (term303 A R f s g).
Proof. exact (TRANS (@lem7032543 A R f s g) (@lem7032542 A R f s g)). Qed.
Lemma lem7032545 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term194 A R f g) = (term304 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7032544 A R f s g)). Qed.
Lemma lem7032546 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7032547 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term196 A R f g) = (term305 A R f g).
Proof. exact (MK_COMB (@lem7032546 A) (@lem7032545 A R f g)). Qed.
Lemma lem7032548 {A : Type'} (R : type1605) (f : A -> nat) : (term198 A R f) = (term306 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7032547 A R f g)). Qed.
Lemma lem7032549 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032550 {A : Type'} (R : type1605) (f : A -> nat) : (term200 A R f) = (term307 A R f).
Proof. exact (MK_COMB (@lem7032549 A) (@lem7032548 A R f)). Qed.
Lemma lem7032551 {A : Type'} (R : type1605) : (term202 A R) = (term308 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7032550 A R f)). Qed.
Lemma lem7032552 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032553 {A : Type'} (R : type1605) : (term204 A R) = (term309 A R).
Proof. exact (MK_COMB (@lem7032552 A) (@lem7032551 A R)). Qed.
Lemma lem7032554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032555 (R : type1605) : (term310 R) = (term311 R).
Proof. exact (MK_COMB (@lem7032554) (@lem7032515 R)). Qed.
Lemma lem7032556 {A : Type'} (R : type1605) : (term312 A R) = (term313 A R).
Proof. exact (MK_COMB (@lem7032555 R) (@lem7032553 A R)). Qed.
Lemma lem7032557 {A : Type'} (R : type1605) : (term205 A R) = (term312 A R).
Proof. exact (@lem17265 (term183 R) (term204 A R)). Qed.
Lemma lem7032558 {A : Type'} (R : type1605) : (term205 A R) = (term313 A R).
Proof. exact (TRANS (@lem7032557 A R) (@lem7032556 A R)). Qed.
Lemma lem7032725 {A : Type'} (P : Prop) (Q : A -> Prop) : (term314 A P Q) = (term315 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7032726 {A : Type'} (P : Prop) (Q : A -> Prop) : (term314 A P Q) = (term315 A P Q).
Proof. exact (@lem7032725 A P Q). Qed.
Lemma lem7032727 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term316 A s R f g) = (term317 A s R f g).
Proof. exact (@lem7032726 A (term318 A s) (term294 A s R f g)). Qed.
Lemma lem7032728 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term319 A s R f g x) = (term285 A s R f g x).
Proof. exact (eq_refl (term319 A s R f g x)). Qed.
Lemma lem7032729 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term320 A s R f g) = (term294 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7032728 A s R f g x)). Qed.
Lemma lem7032730 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7032731 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term321 A s R f g) = (term295 A s R f g).
Proof. exact (MK_COMB (@lem7032730 A) (@lem7032729 A s R f g)). Qed.
Lemma lem7032732 {A : Type'} (s : A -> Prop) : (term296 A s) = (term296 A s).
Proof. exact (eq_refl (term296 A s)). Qed.
Lemma lem7032733 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term316 A s R f g) = (term298 A s R f g).
Proof. exact (MK_COMB (@lem7032732 A s) (@lem7032731 A s R f g)). Qed.
Lemma lem7032734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032735 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term322 A s R f g) = (term323 A s R f g).
Proof. exact (MK_COMB (@lem7032734) (@lem7032733 A s R f g)). Qed.
Lemma lem7032736 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term319 A s R f g x) = (term285 A s R f g x).
Proof. exact (eq_refl (term319 A s R f g x)). Qed.
Lemma lem7032737 {A : Type'} (s : A -> Prop) : (term296 A s) = (term296 A s).
Proof. exact (eq_refl (term296 A s)). Qed.
Lemma lem7032738 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term324 A s R f g x) = (term325 A s R f g x).
Proof. exact (MK_COMB (@lem7032737 A s) (@lem7032736 A s R f g x)). Qed.
Lemma lem7032739 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term326 A s R f g) = (term327 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7032738 A s R f g x)). Qed.
Lemma lem7032740 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7032741 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term317 A s R f g) = (term328 A s R f g).
Proof. exact (MK_COMB (@lem7032740 A) (@lem7032739 A s R f g)). Qed.
Lemma lem7032742 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : ((term316 A s R f g) = (term317 A s R f g)) = ((term298 A s R f g) = (term328 A s R f g)).
Proof. exact (MK_COMB (@lem7032735 A s R f g) (@lem7032741 A s R f g)). Qed.
Lemma lem7032743 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term298 A s R f g) = (term328 A s R f g).
Proof. exact (EQ_MP (@lem7032742 A s R f g) (@lem7032727 A s R f g)). Qed.
Lemma lem7032744 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032745 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term301 A s R f g) = (term329 A s R f g).
Proof. exact (MK_COMB (@lem7032744) (@lem7032743 A s R f g)). Qed.
Lemma lem7032746 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7032747 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term303 A R f s g) = (term330 A R f s g).
Proof. exact (MK_COMB (@lem7032745 A s R f g) (@lem7032746 A R f s g)). Qed.
Lemma lem7032749 {A : Type'} (P : A -> Prop) (Q : Prop) : (term331 A P Q) = (term332 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7032750 {A : Type'} (P : A -> Prop) (Q : Prop) : (term331 A P Q) = (term332 A P Q).
Proof. exact (@lem7032749 A P Q). Qed.
Lemma lem7032751 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term333 A R f s g) = (term334 A R f s g).
Proof. exact (@lem7032750 A (term327 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7032752 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term335 A s R f g x) = (term325 A s R f g x).
Proof. exact (eq_refl (term335 A s R f g x)). Qed.
Lemma lem7032753 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term336 A s R f g) = (term327 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7032752 A s R f g x)). Qed.
Lemma lem7032754 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7032755 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term337 A s R f g) = (term328 A s R f g).
Proof. exact (MK_COMB (@lem7032754 A) (@lem7032753 A s R f g)). Qed.
Lemma lem7032756 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032757 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term338 A s R f g) = (term329 A s R f g).
Proof. exact (MK_COMB (@lem7032756) (@lem7032755 A s R f g)). Qed.
Lemma lem7032758 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7032759 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term333 A R f s g) = (term330 A R f s g).
Proof. exact (MK_COMB (@lem7032757 A s R f g) (@lem7032758 A R f s g)). Qed.
Lemma lem7032760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032761 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term339 A R f s g) = (term340 A R f s g).
Proof. exact (MK_COMB (@lem7032760) (@lem7032759 A R f s g)). Qed.
Lemma lem7032762 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term335 A s R f g x) = (term325 A s R f g x).
Proof. exact (eq_refl (term335 A s R f g x)). Qed.
Lemma lem7032763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032764 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term341 A s R f g x) = (term342 A s R f g x).
Proof. exact (MK_COMB (@lem7032763) (@lem7032762 A s R f g x)). Qed.
Lemma lem7032765 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7032766 {A : Type'} (x : A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term343 A x R f s g) = (term344 A x R f s g).
Proof. exact (MK_COMB (@lem7032764 A s R f g x) (@lem7032765 A R f s g)). Qed.
Lemma lem7032767 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term345 A R f s g) = (term346 A R f s g).
Proof. exact (fun_ext (fun x : A => @lem7032766 A x R f s g)). Qed.
Lemma lem7032768 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7032769 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term334 A R f s g) = (term347 A R f s g).
Proof. exact (MK_COMB (@lem7032768 A) (@lem7032767 A R f s g)). Qed.
Lemma lem7032770 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((term333 A R f s g) = (term334 A R f s g)) = ((term330 A R f s g) = (term347 A R f s g)).
Proof. exact (MK_COMB (@lem7032761 A R f s g) (@lem7032769 A R f s g)). Qed.
Lemma lem7032771 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term330 A R f s g) = (term347 A R f s g).
Proof. exact (EQ_MP (@lem7032770 A R f s g) (@lem7032751 A R f s g)). Qed.
Lemma lem7032772 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term303 A R f s g) = (term347 A R f s g).
Proof. exact (TRANS (@lem7032747 A R f s g) (@lem7032771 A R f s g)). Qed.
Lemma lem7032773 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term304 A R f g) = (term348 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7032772 A R f s g)). Qed.
Lemma lem7032774 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7032775 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term305 A R f g) = (term349 A R f g).
Proof. exact (MK_COMB (@lem7032774 A) (@lem7032773 A R f g)). Qed.
Lemma lem7032777 {A B : Type'} (P : type1413 A B) : (term350 A B P) = (term351 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7032778 {A : Type'} (P : type672 A) : (term352 A P) = (term353 A P).
Proof. exact (@lem7032777 (A -> Prop) A P). Qed.
Lemma lem7032779 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term354 A R f g) = (term355 A R f g).
Proof. exact (@lem7032778 A (term356 A R f g)). Qed.
Lemma lem7032780 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term357 A R f g s) = (term346 A R f s g).
Proof. exact (eq_refl (term357 A R f g s)). Qed.
Lemma lem7032781 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7032782 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term358 A R f g s x) = (term359 A R f s g x).
Proof. exact (MK_COMB (@lem7032780 A R f s g) (@lem7032781 A x)). Qed.
Lemma lem7032783 {A : Type'} (x : A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term359 A R f s g x) = (term344 A x R f s g).
Proof. exact (eq_refl (term359 A R f s g x)). Qed.
Lemma lem7032784 {A : Type'} (x : A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term358 A R f g s x) = (term344 A x R f s g).
Proof. exact (TRANS (@lem7032782 A R f s g x) (@lem7032783 A x R f s g)). Qed.
Lemma lem7032785 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term360 A R f g s) = (term346 A R f s g).
Proof. exact (fun_ext (fun x : A => @lem7032784 A x R f s g)). Qed.
Lemma lem7032786 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7032787 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term361 A R f g s) = (term347 A R f s g).
Proof. exact (MK_COMB (@lem7032786 A) (@lem7032785 A R f s g)). Qed.
Lemma lem7032788 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term362 A R f g) = (term348 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7032787 A R f s g)). Qed.
Lemma lem7032789 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7032790 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term354 A R f g) = (term349 A R f g).
Proof. exact (MK_COMB (@lem7032789 A) (@lem7032788 A R f g)). Qed.
Lemma lem7032791 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032792 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term363 A R f g) = (term364 A R f g).
Proof. exact (MK_COMB (@lem7032791) (@lem7032790 A R f g)). Qed.
Lemma lem7032793 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term357 A R f g s) = (term346 A R f s g).
Proof. exact (eq_refl (term357 A R f g s)). Qed.
Lemma lem7032794 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7032795 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : type684 A) (s : A -> Prop) : (term365 A R f g x s) = (term366 A R f g x s).
Proof. exact (MK_COMB (@lem7032793 A R f s g) (@lem7032794 A x s)). Qed.
Lemma lem7032796 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term366 A R f g x s) = (term367 A x R f s g).
Proof. exact (eq_refl (term366 A R f g x s)). Qed.
Lemma lem7032797 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term365 A R f g x s) = (term367 A x R f s g).
Proof. exact (TRANS (@lem7032795 A R f g x s) (@lem7032796 A x R f s g)). Qed.
Lemma lem7032798 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term368 A R f g x) = (term369 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7032797 A x R f s g)). Qed.
Lemma lem7032799 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7032800 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term370 A R f g x) = (term371 A x R f g).
Proof. exact (MK_COMB (@lem7032799 A) (@lem7032798 A x R f g)). Qed.
Lemma lem7032801 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term372 A R f g) = (term373 A R f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7032800 A x R f g)). Qed.
Lemma lem7032802 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7032803 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term355 A R f g) = (term374 A R f g).
Proof. exact (MK_COMB (@lem7032802 A) (@lem7032801 A R f g)). Qed.
Lemma lem7032804 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : ((term354 A R f g) = (term355 A R f g)) = ((term349 A R f g) = (term374 A R f g)).
Proof. exact (MK_COMB (@lem7032792 A R f g) (@lem7032803 A R f g)). Qed.
Lemma lem7032805 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term349 A R f g) = (term374 A R f g).
Proof. exact (EQ_MP (@lem7032804 A R f g) (@lem7032779 A R f g)). Qed.
Lemma lem7032806 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term305 A R f g) = (term374 A R f g).
Proof. exact (TRANS (@lem7032775 A R f g) (@lem7032805 A R f g)). Qed.
Lemma lem7032807 {A : Type'} (R : type1605) (f : A -> nat) : (term306 A R f) = (term375 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7032806 A R f g)). Qed.
Lemma lem7032808 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032809 {A : Type'} (R : type1605) (f : A -> nat) : (term307 A R f) = (term376 A R f).
Proof. exact (MK_COMB (@lem7032808 A) (@lem7032807 A R f)). Qed.
Lemma lem7032811 {A B : Type'} (P : type1413 A B) : (term350 A B P) = (term351 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7032812 {A : Type'} (P : type690 A) : (term377 A P) = (term378 A P).
Proof. exact (@lem7032811 (A -> nat) (type684 A) P). Qed.
Lemma lem7032813 {A : Type'} (R : type1605) (f : A -> nat) : (term379 A R f) = (term380 A R f).
Proof. exact (@lem7032812 A (term381 A R f)). Qed.
Lemma lem7032814 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term382 A R f g) = (term373 A R f g).
Proof. exact (eq_refl (term382 A R f g)). Qed.
Lemma lem7032815 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7032816 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : type684 A) : (term383 A R f g x) = (term384 A R f g x).
Proof. exact (MK_COMB (@lem7032814 A R f g) (@lem7032815 A x)). Qed.
Lemma lem7032817 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term384 A R f g x) = (term371 A x R f g).
Proof. exact (eq_refl (term384 A R f g x)). Qed.
Lemma lem7032818 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term383 A R f g x) = (term371 A x R f g).
Proof. exact (TRANS (@lem7032816 A R f g x) (@lem7032817 A x R f g)). Qed.
Lemma lem7032819 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term385 A R f g) = (term373 A R f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7032818 A x R f g)). Qed.
Lemma lem7032820 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7032821 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term386 A R f g) = (term374 A R f g).
Proof. exact (MK_COMB (@lem7032820 A) (@lem7032819 A R f g)). Qed.
Lemma lem7032822 {A : Type'} (R : type1605) (f : A -> nat) : (term387 A R f) = (term375 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7032821 A R f g)). Qed.
Lemma lem7032823 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032824 {A : Type'} (R : type1605) (f : A -> nat) : (term379 A R f) = (term376 A R f).
Proof. exact (MK_COMB (@lem7032823 A) (@lem7032822 A R f)). Qed.
Lemma lem7032825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032826 {A : Type'} (R : type1605) (f : A -> nat) : (term388 A R f) = (term389 A R f).
Proof. exact (MK_COMB (@lem7032825) (@lem7032824 A R f)). Qed.
Lemma lem7032827 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term382 A R f g) = (term373 A R f g).
Proof. exact (eq_refl (term382 A R f g)). Qed.
Lemma lem7032828 {A : Type'} (x : type694 A) (g : A -> nat) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7032829 {A : Type'} (R : type1605) (f : A -> nat) (x : type694 A) (g : A -> nat) : (term390 A R f x g) = (term391 A R f x g).
Proof. exact (MK_COMB (@lem7032827 A R f g) (@lem7032828 A x g)). Qed.
Lemma lem7032830 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term391 A R f x g) = (term392 A x R f g).
Proof. exact (eq_refl (term391 A R f x g)). Qed.
Lemma lem7032831 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term390 A R f x g) = (term392 A x R f g).
Proof. exact (TRANS (@lem7032829 A R f x g) (@lem7032830 A x R f g)). Qed.
Lemma lem7032832 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) : (term393 A R f x) = (term394 A x R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7032831 A x R f g)). Qed.
Lemma lem7032833 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032834 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) : (term395 A R f x) = (term396 A x R f).
Proof. exact (MK_COMB (@lem7032833 A) (@lem7032832 A x R f)). Qed.
Lemma lem7032835 {A : Type'} (R : type1605) (f : A -> nat) : (term397 A R f) = (term398 A R f).
Proof. exact (fun_ext (fun x : type694 A => @lem7032834 A x R f)). Qed.
Lemma lem7032836 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7032837 {A : Type'} (R : type1605) (f : A -> nat) : (term380 A R f) = (term399 A R f).
Proof. exact (MK_COMB (@lem7032836 A) (@lem7032835 A R f)). Qed.
Lemma lem7032838 {A : Type'} (R : type1605) (f : A -> nat) : ((term379 A R f) = (term380 A R f)) = ((term376 A R f) = (term399 A R f)).
Proof. exact (MK_COMB (@lem7032826 A R f) (@lem7032837 A R f)). Qed.
Lemma lem7032839 {A : Type'} (R : type1605) (f : A -> nat) : (term376 A R f) = (term399 A R f).
Proof. exact (EQ_MP (@lem7032838 A R f) (@lem7032813 A R f)). Qed.
Lemma lem7032840 {A : Type'} (R : type1605) (f : A -> nat) : (term307 A R f) = (term399 A R f).
Proof. exact (TRANS (@lem7032809 A R f) (@lem7032839 A R f)). Qed.
Lemma lem7032841 {A : Type'} (R : type1605) : (term308 A R) = (term400 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7032840 A R f)). Qed.
Lemma lem7032842 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032843 {A : Type'} (R : type1605) : (term309 A R) = (term401 A R).
Proof. exact (MK_COMB (@lem7032842 A) (@lem7032841 A R)). Qed.
Lemma lem7032845 {A B : Type'} (P : type1413 A B) : (term350 A B P) = (term351 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7032846 {A : Type'} (P : type691 A) : (term402 A P) = (term403 A P).
Proof. exact (@lem7032845 (A -> nat) (type694 A) P). Qed.
Lemma lem7032847 {A : Type'} (R : type1605) : (term404 A R) = (term405 A R).
Proof. exact (@lem7032846 A (term406 A R)). Qed.
Lemma lem7032848 {A : Type'} (R : type1605) (f : A -> nat) : (term407 A R f) = (term398 A R f).
Proof. exact (eq_refl (term407 A R f)). Qed.
Lemma lem7032849 {A : Type'} (x : type694 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7032850 {A : Type'} (R : type1605) (f : A -> nat) (x : type694 A) : (term408 A R f x) = (term409 A R f x).
Proof. exact (MK_COMB (@lem7032848 A R f) (@lem7032849 A x)). Qed.
Lemma lem7032851 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) : (term409 A R f x) = (term396 A x R f).
Proof. exact (eq_refl (term409 A R f x)). Qed.
Lemma lem7032852 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) : (term408 A R f x) = (term396 A x R f).
Proof. exact (TRANS (@lem7032850 A R f x) (@lem7032851 A x R f)). Qed.
Lemma lem7032853 {A : Type'} (R : type1605) (f : A -> nat) : (term410 A R f) = (term398 A R f).
Proof. exact (fun_ext (fun x : type694 A => @lem7032852 A x R f)). Qed.
Lemma lem7032854 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7032855 {A : Type'} (R : type1605) (f : A -> nat) : (term411 A R f) = (term399 A R f).
Proof. exact (MK_COMB (@lem7032854 A) (@lem7032853 A R f)). Qed.
Lemma lem7032856 {A : Type'} (R : type1605) : (term412 A R) = (term400 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7032855 A R f)). Qed.
Lemma lem7032857 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032858 {A : Type'} (R : type1605) : (term404 A R) = (term401 A R).
Proof. exact (MK_COMB (@lem7032857 A) (@lem7032856 A R)). Qed.
Lemma lem7032859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032860 {A : Type'} (R : type1605) : (term413 A R) = (term414 A R).
Proof. exact (MK_COMB (@lem7032859) (@lem7032858 A R)). Qed.
Lemma lem7032861 {A : Type'} (R : type1605) (f : A -> nat) : (term407 A R f) = (term398 A R f).
Proof. exact (eq_refl (term407 A R f)). Qed.
Lemma lem7032862 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7032863 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) : (term415 A R x f) = (term416 A R x f).
Proof. exact (MK_COMB (@lem7032861 A R f) (@lem7032862 A x f)). Qed.
Lemma lem7032864 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term416 A R x f) = (term417 A x R f).
Proof. exact (eq_refl (term416 A R x f)). Qed.
Lemma lem7032865 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term415 A R x f) = (term417 A x R f).
Proof. exact (TRANS (@lem7032863 A R x f) (@lem7032864 A x R f)). Qed.
Lemma lem7032866 {A : Type'} (x : type695 A) (R : type1605) : (term418 A R x) = (term419 A x R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7032865 A x R f)). Qed.
Lemma lem7032867 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7032868 {A : Type'} (x : type695 A) (R : type1605) : (term420 A R x) = (term421 A x R).
Proof. exact (MK_COMB (@lem7032867 A) (@lem7032866 A x R)). Qed.
Lemma lem7032869 {A : Type'} (R : type1605) : (term422 A R) = (term423 A R).
Proof. exact (fun_ext (fun x : type695 A => @lem7032868 A x R)). Qed.
Lemma lem7032870 {A : Type'} : (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7032871 {A : Type'} (R : type1605) : (term405 A R) = (term424 A R).
Proof. exact (MK_COMB (@lem7032870 A) (@lem7032869 A R)). Qed.
Lemma lem7032872 {A : Type'} (R : type1605) : ((term404 A R) = (term405 A R)) = ((term401 A R) = (term424 A R)).
Proof. exact (MK_COMB (@lem7032860 A R) (@lem7032871 A R)). Qed.
Lemma lem7032873 {A : Type'} (R : type1605) : (term401 A R) = (term424 A R).
Proof. exact (EQ_MP (@lem7032872 A R) (@lem7032847 A R)). Qed.
Lemma lem7032874 {A : Type'} (R : type1605) : (term309 A R) = (term424 A R).
Proof. exact (TRANS (@lem7032843 A R) (@lem7032873 A R)). Qed.
Lemma lem7032875 (R : type1605) : (term311 R) = (term311 R).
Proof. exact (eq_refl (term311 R)). Qed.
Lemma lem7032876 {A : Type'} (R : type1605) : (term313 A R) = (term425 A R).
Proof. exact (MK_COMB (@lem7032875 R) (@lem7032874 A R)). Qed.
Lemma lem7032880 {A : Type'} (P : A -> Prop) (Q : Prop) : (term331 A P Q) = (term332 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7032881 (P : nat -> Prop) (Q : Prop) : (term426 P Q) = (term427 P Q).
Proof. exact (@lem7032880 nat P Q). Qed.
Lemma lem7032882 {A : Type'} (R : type1605) : (term428 A R) = (term429 A R).
Proof. exact (@lem7032881 (term282 R) (term424 A R)). Qed.
Lemma lem7032883 (R : type1605) (x1 : nat) : (term430 R x1) = (term276 R x1).
Proof. exact (eq_refl (term430 R x1)). Qed.
Lemma lem7032884 (R : type1605) : (term431 R) = (term282 R).
Proof. exact (fun_ext (fun x1 : nat => @lem7032883 R x1)). Qed.
Lemma lem7032885 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032886 (R : type1605) : (term432 R) = (term283 R).
Proof. exact (MK_COMB (@lem7032885) (@lem7032884 R)). Qed.
Lemma lem7032887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032888 (R : type1605) : (term433 R) = (term311 R).
Proof. exact (MK_COMB (@lem7032887) (@lem7032886 R)). Qed.
Lemma lem7032889 {A : Type'} (R : type1605) : (term424 A R) = (term424 A R).
Proof. exact (eq_refl (term424 A R)). Qed.
Lemma lem7032890 {A : Type'} (R : type1605) : (term428 A R) = (term425 A R).
Proof. exact (MK_COMB (@lem7032888 R) (@lem7032889 A R)). Qed.
Lemma lem7032891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032892 {A : Type'} (R : type1605) : (term434 A R) = (term435 A R).
Proof. exact (MK_COMB (@lem7032891) (@lem7032890 A R)). Qed.
Lemma lem7032893 (R : type1605) (x1 : nat) : (term430 R x1) = (term276 R x1).
Proof. exact (eq_refl (term430 R x1)). Qed.
Lemma lem7032894 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032895 (R : type1605) (x1 : nat) : (term436 R x1) = (term437 R x1).
Proof. exact (MK_COMB (@lem7032894) (@lem7032893 R x1)). Qed.
Lemma lem7032896 {A : Type'} (R : type1605) : (term424 A R) = (term424 A R).
Proof. exact (eq_refl (term424 A R)). Qed.
Lemma lem7032897 {A : Type'} (x1 : nat) (R : type1605) : (term438 A x1 R) = (term439 A x1 R).
Proof. exact (MK_COMB (@lem7032895 R x1) (@lem7032896 A R)). Qed.
Lemma lem7032898 {A : Type'} (R : type1605) : (term440 A R) = (term441 A R).
Proof. exact (fun_ext (fun x1 : nat => @lem7032897 A x1 R)). Qed.
Lemma lem7032899 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032900 {A : Type'} (R : type1605) : (term429 A R) = (term442 A R).
Proof. exact (MK_COMB (@lem7032899) (@lem7032898 A R)). Qed.
Lemma lem7032901 {A : Type'} (R : type1605) : ((term428 A R) = (term429 A R)) = ((term425 A R) = (term442 A R)).
Proof. exact (MK_COMB (@lem7032892 A R) (@lem7032900 A R)). Qed.
Lemma lem7032902 {A : Type'} (R : type1605) : (term425 A R) = (term442 A R).
Proof. exact (EQ_MP (@lem7032901 A R) (@lem7032882 A R)). Qed.
Lemma lem7032906 {A : Type'} (P : A -> Prop) (Q : Prop) : (term331 A P Q) = (term332 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7032907 (P : nat -> Prop) (Q : Prop) : (term426 P Q) = (term427 P Q).
Proof. exact (@lem7032906 nat P Q). Qed.
Lemma lem7032908 {A : Type'} (x1 : nat) (R : type1605) : (term443 A x1 R) = (term444 A x1 R).
Proof. exact (@lem7032907 (term275 R x1) (term424 A R)). Qed.
Lemma lem7032909 (R : type1605) (x1 : nat) (y1 : nat) : (term445 R x1 y1) = (term269 R x1 y1).
Proof. exact (eq_refl (term445 R x1 y1)). Qed.
Lemma lem7032910 (R : type1605) (x1 : nat) : (term446 R x1) = (term275 R x1).
Proof. exact (fun_ext (fun y1 : nat => @lem7032909 R x1 y1)). Qed.
Lemma lem7032911 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032912 (R : type1605) (x1 : nat) : (term447 R x1) = (term276 R x1).
Proof. exact (MK_COMB (@lem7032911) (@lem7032910 R x1)). Qed.
Lemma lem7032913 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032914 (R : type1605) (x1 : nat) : (term448 R x1) = (term437 R x1).
Proof. exact (MK_COMB (@lem7032913) (@lem7032912 R x1)). Qed.
Lemma lem7032915 {A : Type'} (R : type1605) : (term424 A R) = (term424 A R).
Proof. exact (eq_refl (term424 A R)). Qed.
Lemma lem7032916 {A : Type'} (x1 : nat) (R : type1605) : (term443 A x1 R) = (term439 A x1 R).
Proof. exact (MK_COMB (@lem7032914 R x1) (@lem7032915 A R)). Qed.
Lemma lem7032917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032918 {A : Type'} (x1 : nat) (R : type1605) : (term449 A x1 R) = (term450 A x1 R).
Proof. exact (MK_COMB (@lem7032917) (@lem7032916 A x1 R)). Qed.
Lemma lem7032919 (R : type1605) (x1 : nat) (y1 : nat) : (term445 R x1 y1) = (term269 R x1 y1).
Proof. exact (eq_refl (term445 R x1 y1)). Qed.
Lemma lem7032920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032921 (R : type1605) (x1 : nat) (y1 : nat) : (term451 R x1 y1) = (term452 R x1 y1).
Proof. exact (MK_COMB (@lem7032920) (@lem7032919 R x1 y1)). Qed.
Lemma lem7032922 {A : Type'} (R : type1605) : (term424 A R) = (term424 A R).
Proof. exact (eq_refl (term424 A R)). Qed.
Lemma lem7032923 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term453 A x1 y1 R) = (term454 A x1 y1 R).
Proof. exact (MK_COMB (@lem7032921 R x1 y1) (@lem7032922 A R)). Qed.
Lemma lem7032924 {A : Type'} (x1 : nat) (R : type1605) : (term455 A x1 R) = (term456 A x1 R).
Proof. exact (fun_ext (fun y1 : nat => @lem7032923 A x1 y1 R)). Qed.
Lemma lem7032925 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032926 {A : Type'} (x1 : nat) (R : type1605) : (term444 A x1 R) = (term457 A x1 R).
Proof. exact (MK_COMB (@lem7032925) (@lem7032924 A x1 R)). Qed.
Lemma lem7032927 {A : Type'} (x1 : nat) (R : type1605) : ((term443 A x1 R) = (term444 A x1 R)) = ((term439 A x1 R) = (term457 A x1 R)).
Proof. exact (MK_COMB (@lem7032918 A x1 R) (@lem7032926 A x1 R)). Qed.
Lemma lem7032928 {A : Type'} (x1 : nat) (R : type1605) : (term439 A x1 R) = (term457 A x1 R).
Proof. exact (EQ_MP (@lem7032927 A x1 R) (@lem7032908 A x1 R)). Qed.
Lemma lem7032932 {A : Type'} (P : A -> Prop) (Q : Prop) : (term331 A P Q) = (term332 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7032933 (P : nat -> Prop) (Q : Prop) : (term426 P Q) = (term427 P Q).
Proof. exact (@lem7032932 nat P Q). Qed.
Lemma lem7032934 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term458 A x1 y1 R) = (term459 A x1 y1 R).
Proof. exact (@lem7032933 (term268 R x1 y1) (term424 A R)). Qed.
Lemma lem7032935 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term460 R x1 y1 x2) = (term262 R x1 y1 x2).
Proof. exact (eq_refl (term460 R x1 y1 x2)). Qed.
Lemma lem7032936 (R : type1605) (x1 : nat) (y1 : nat) : (term461 R x1 y1) = (term268 R x1 y1).
Proof. exact (fun_ext (fun x2 : nat => @lem7032935 R x1 y1 x2)). Qed.
Lemma lem7032937 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032938 (R : type1605) (x1 : nat) (y1 : nat) : (term462 R x1 y1) = (term269 R x1 y1).
Proof. exact (MK_COMB (@lem7032937) (@lem7032936 R x1 y1)). Qed.
Lemma lem7032939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032940 (R : type1605) (x1 : nat) (y1 : nat) : (term463 R x1 y1) = (term452 R x1 y1).
Proof. exact (MK_COMB (@lem7032939) (@lem7032938 R x1 y1)). Qed.
Lemma lem7032941 {A : Type'} (R : type1605) : (term424 A R) = (term424 A R).
Proof. exact (eq_refl (term424 A R)). Qed.
Lemma lem7032942 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term458 A x1 y1 R) = (term454 A x1 y1 R).
Proof. exact (MK_COMB (@lem7032940 R x1 y1) (@lem7032941 A R)). Qed.
Lemma lem7032943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032944 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term464 A x1 y1 R) = (term465 A x1 y1 R).
Proof. exact (MK_COMB (@lem7032943) (@lem7032942 A x1 y1 R)). Qed.
Lemma lem7032945 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term460 R x1 y1 x2) = (term262 R x1 y1 x2).
Proof. exact (eq_refl (term460 R x1 y1 x2)). Qed.
Lemma lem7032946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032947 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term466 R x1 y1 x2) = (term467 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7032946) (@lem7032945 R x1 y1 x2)). Qed.
Lemma lem7032948 {A : Type'} (R : type1605) : (term424 A R) = (term424 A R).
Proof. exact (eq_refl (term424 A R)). Qed.
Lemma lem7032949 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term468 A x1 y1 x2 R) = (term469 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7032947 R x1 y1 x2) (@lem7032948 A R)). Qed.
Lemma lem7032950 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term470 A x1 y1 R) = (term471 A x1 y1 R).
Proof. exact (fun_ext (fun x2 : nat => @lem7032949 A x1 y1 x2 R)). Qed.
Lemma lem7032951 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032952 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term459 A x1 y1 R) = (term472 A x1 y1 R).
Proof. exact (MK_COMB (@lem7032951) (@lem7032950 A x1 y1 R)). Qed.
Lemma lem7032953 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : ((term458 A x1 y1 R) = (term459 A x1 y1 R)) = ((term454 A x1 y1 R) = (term472 A x1 y1 R)).
Proof. exact (MK_COMB (@lem7032944 A x1 y1 R) (@lem7032952 A x1 y1 R)). Qed.
Lemma lem7032954 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term454 A x1 y1 R) = (term472 A x1 y1 R).
Proof. exact (EQ_MP (@lem7032953 A x1 y1 R) (@lem7032934 A x1 y1 R)). Qed.
Lemma lem7032958 {A : Type'} (P : A -> Prop) (Q : Prop) : (term331 A P Q) = (term332 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7032959 (P : nat -> Prop) (Q : Prop) : (term426 P Q) = (term427 P Q).
Proof. exact (@lem7032958 nat P Q). Qed.
Lemma lem7032960 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term473 A x1 y1 x2 R) = (term474 A x1 y1 x2 R).
Proof. exact (@lem7032959 (term261 R x1 y1 x2) (term424 A R)). Qed.
Lemma lem7032961 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term475 R x1 y1 x2 y2) = (term252 R x1 y1 x2 y2).
Proof. exact (eq_refl (term475 R x1 y1 x2 y2)). Qed.
Lemma lem7032962 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term476 R x1 y1 x2) = (term261 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : nat => @lem7032961 R x1 y1 x2 y2)). Qed.
Lemma lem7032963 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032964 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term477 R x1 y1 x2) = (term262 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7032963) (@lem7032962 R x1 y1 x2)). Qed.
Lemma lem7032965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032966 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term478 R x1 y1 x2) = (term467 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7032965) (@lem7032964 R x1 y1 x2)). Qed.
Lemma lem7032967 {A : Type'} (R : type1605) : (term424 A R) = (term424 A R).
Proof. exact (eq_refl (term424 A R)). Qed.
Lemma lem7032968 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term473 A x1 y1 x2 R) = (term469 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7032966 R x1 y1 x2) (@lem7032967 A R)). Qed.
Lemma lem7032969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032970 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term479 A x1 y1 x2 R) = (term480 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7032969) (@lem7032968 A x1 y1 x2 R)). Qed.
Lemma lem7032971 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term475 R x1 y1 x2 y2) = (term252 R x1 y1 x2 y2).
Proof. exact (eq_refl (term475 R x1 y1 x2 y2)). Qed.
Lemma lem7032972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7032973 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term481 R x1 y1 x2 y2) = (term482 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7032972) (@lem7032971 R x1 y1 x2 y2)). Qed.
Lemma lem7032974 {A : Type'} (R : type1605) : (term424 A R) = (term424 A R).
Proof. exact (eq_refl (term424 A R)). Qed.
Lemma lem7032975 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term483 A x1 y1 x2 y2 R) = (term484 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7032973 R x1 y1 x2 y2) (@lem7032974 A R)). Qed.
Lemma lem7032976 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term485 A x1 y1 x2 R) = (term486 A x1 y1 x2 R).
Proof. exact (fun_ext (fun y2 : nat => @lem7032975 A x1 y1 x2 y2 R)). Qed.
Lemma lem7032977 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7032978 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term474 A x1 y1 x2 R) = (term487 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7032977) (@lem7032976 A x1 y1 x2 R)). Qed.
Lemma lem7032979 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : ((term473 A x1 y1 x2 R) = (term474 A x1 y1 x2 R)) = ((term469 A x1 y1 x2 R) = (term487 A x1 y1 x2 R)).
Proof. exact (MK_COMB (@lem7032970 A x1 y1 x2 R) (@lem7032978 A x1 y1 x2 R)). Qed.
Lemma lem7032980 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term469 A x1 y1 x2 R) = (term487 A x1 y1 x2 R).
Proof. exact (EQ_MP (@lem7032979 A x1 y1 x2 R) (@lem7032960 A x1 y1 x2 R)). Qed.
Lemma lem7032982 {A : Type'} (P : Prop) (Q : A -> Prop) : (term314 A P Q) = (term315 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7032983 {A : Type'} (P : Prop) (Q : type181 A) : (term488 A P Q) = (term489 A P Q).
Proof. exact (@lem7032982 (type695 A) P Q). Qed.
Lemma lem7032984 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term490 A x1 y1 x2 y2 R) = (term491 A x1 y1 x2 y2 R).
Proof. exact (@lem7032983 A (term252 R x1 y1 x2 y2) (term423 A R)). Qed.
Lemma lem7032985 {A : Type'} (x : type695 A) (R : type1605) : (term492 A R x) = (term421 A x R).
Proof. exact (eq_refl (term492 A R x)). Qed.
Lemma lem7032986 {A : Type'} (R : type1605) : (term493 A R) = (term423 A R).
Proof. exact (fun_ext (fun x : type695 A => @lem7032985 A x R)). Qed.
Lemma lem7032987 {A : Type'} : (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7032988 {A : Type'} (R : type1605) : (term494 A R) = (term424 A R).
Proof. exact (MK_COMB (@lem7032987 A) (@lem7032986 A R)). Qed.
Lemma lem7032989 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term482 R x1 y1 x2 y2) = (term482 R x1 y1 x2 y2).
Proof. exact (eq_refl (term482 R x1 y1 x2 y2)). Qed.
Lemma lem7032990 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term490 A x1 y1 x2 y2 R) = (term484 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7032989 R x1 y1 x2 y2) (@lem7032988 A R)). Qed.
Lemma lem7032991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7032992 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term495 A x1 y1 x2 y2 R) = (term496 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7032991) (@lem7032990 A x1 y1 x2 y2 R)). Qed.
Lemma lem7032993 {A : Type'} (x : type695 A) (R : type1605) : (term492 A R x) = (term421 A x R).
Proof. exact (eq_refl (term492 A R x)). Qed.
Lemma lem7032994 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term482 R x1 y1 x2 y2) = (term482 R x1 y1 x2 y2).
Proof. exact (eq_refl (term482 R x1 y1 x2 y2)). Qed.
Lemma lem7032995 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) : (term497 A x1 y1 x2 y2 R x) = (term498 A x1 y1 x2 y2 x R).
Proof. exact (MK_COMB (@lem7032994 R x1 y1 x2 y2) (@lem7032993 A x R)). Qed.
Lemma lem7032996 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term499 A x1 y1 x2 y2 R) = (term500 A x1 y1 x2 y2 R).
Proof. exact (fun_ext (fun x : type695 A => @lem7032995 A x1 y1 x2 y2 x R)). Qed.
Lemma lem7032997 {A : Type'} : (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7032998 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term491 A x1 y1 x2 y2 R) = (term501 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7032997 A) (@lem7032996 A x1 y1 x2 y2 R)). Qed.
Lemma lem7032999 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : ((term490 A x1 y1 x2 y2 R) = (term491 A x1 y1 x2 y2 R)) = ((term484 A x1 y1 x2 y2 R) = (term501 A x1 y1 x2 y2 R)).
Proof. exact (MK_COMB (@lem7032992 A x1 y1 x2 y2 R) (@lem7032998 A x1 y1 x2 y2 R)). Qed.
Lemma lem7033000 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term484 A x1 y1 x2 y2 R) = (term501 A x1 y1 x2 y2 R).
Proof. exact (EQ_MP (@lem7032999 A x1 y1 x2 y2 R) (@lem7032984 A x1 y1 x2 y2 R)). Qed.
Lemma lem7033001 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term486 A x1 y1 x2 R) = (term502 A x1 y1 x2 R).
Proof. exact (fun_ext (fun y2 : nat => @lem7033000 A x1 y1 x2 y2 R)). Qed.
Lemma lem7033002 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7033003 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term487 A x1 y1 x2 R) = (term503 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7033002) (@lem7033001 A x1 y1 x2 R)). Qed.
Lemma lem7033004 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term469 A x1 y1 x2 R) = (term503 A x1 y1 x2 R).
Proof. exact (TRANS (@lem7032980 A x1 y1 x2 R) (@lem7033003 A x1 y1 x2 R)). Qed.
Lemma lem7033005 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term471 A x1 y1 R) = (term504 A x1 y1 R).
Proof. exact (fun_ext (fun x2 : nat => @lem7033004 A x1 y1 x2 R)). Qed.
Lemma lem7033006 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7033007 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term472 A x1 y1 R) = (term505 A x1 y1 R).
Proof. exact (MK_COMB (@lem7033006) (@lem7033005 A x1 y1 R)). Qed.
Lemma lem7033008 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term454 A x1 y1 R) = (term505 A x1 y1 R).
Proof. exact (TRANS (@lem7032954 A x1 y1 R) (@lem7033007 A x1 y1 R)). Qed.
Lemma lem7033009 {A : Type'} (x1 : nat) (R : type1605) : (term456 A x1 R) = (term506 A x1 R).
Proof. exact (fun_ext (fun y1 : nat => @lem7033008 A x1 y1 R)). Qed.
Lemma lem7033010 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7033011 {A : Type'} (x1 : nat) (R : type1605) : (term457 A x1 R) = (term507 A x1 R).
Proof. exact (MK_COMB (@lem7033010) (@lem7033009 A x1 R)). Qed.
Lemma lem7033012 {A : Type'} (x1 : nat) (R : type1605) : (term439 A x1 R) = (term507 A x1 R).
Proof. exact (TRANS (@lem7032928 A x1 R) (@lem7033011 A x1 R)). Qed.
Lemma lem7033013 {A : Type'} (R : type1605) : (term441 A R) = (term508 A R).
Proof. exact (fun_ext (fun x1 : nat => @lem7033012 A x1 R)). Qed.
Lemma lem7033014 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7033015 {A : Type'} (R : type1605) : (term442 A R) = (term509 A R).
Proof. exact (MK_COMB (@lem7033014) (@lem7033013 A R)). Qed.
Lemma lem7033016 {A : Type'} (R : type1605) : (term425 A R) = (term509 A R).
Proof. exact (TRANS (@lem7032902 A R) (@lem7033015 A R)). Qed.
Lemma lem7033018 {A : Type'} (R : type1605) : (term313 A R) = (term509 A R).
Proof. exact (TRANS (@lem7032876 A R) (@lem7033016 A R)). Qed.
Lemma lem7033019 {A : Type'} (R : type1605) : (term205 A R) = (term509 A R).
Proof. exact (TRANS (@lem7032558 A R) (@lem7033018 A R)). Qed.
Lemma lem7033020 {A : Type'} (R : type1605) (h1 : term205 A R) : term509 A R.
Proof. exact (EQ_MP (@lem7033019 A R) (@lem7032317 A R h1)). Qed.
Lemma lem7033026 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7033033 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term226 A s R f g x) = (term510 A s R f g x).
Proof. exact (@lem17265 (@IN A x s) (term286 A R f g x)). Qed.
Lemma lem7033034 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term227 A s R f g) = (term511 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7033033 A s R f g x)). Qed.
Lemma lem7033035 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7033088 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term80 A s R f g) = (term512 A s R f g).
Proof. exact (MK_COMB (@lem7033035 A) (@lem7033034 A s R f g)). Qed.
Lemma lem7033089 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term512 A s R f g.
Proof. exact (EQ_MP (@lem7033088 A s R f g) (@lem7032319 A s R f g h1)). Qed.
Lemma lem7033095 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term238 A R f s g) : term238 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7033096 {A : Type'} (x1 : nat) (R : type1605) (h1 : term507 A x1 R) : term507 A x1 R.
Proof. exact (h1). Qed.
Lemma lem7033097 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) (h1 : term505 A x1 y1 R) : term505 A x1 y1 R.
Proof. exact (h1). Qed.
Lemma lem7033098 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) (h1 : term503 A x1 y1 x2 R) : term503 A x1 y1 x2 R.
Proof. exact (h1). Qed.
Lemma lem7033099 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) (h1 : term501 A x1 y1 x2 y2 R) : term501 A x1 y1 x2 y2 R.
Proof. exact (h1). Qed.
Lemma lem7033100 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) (h1 : term498 A x1 y1 x2 y2 x R) : term498 A x1 y1 x2 y2 x R.
Proof. exact (h1). Qed.
Lemma lem7033133 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7033140 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033141 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7033140 nat (nat -> nat) f x). Qed.
Lemma lem7033142 (m : nat) : (Nat.add m) = (@I (nat -> nat -> nat) Nat.add m).
Proof. exact (@lem7033141 Nat.add m). Qed.
Lemma lem7033143 (m' : nat) : m' = m'.
Proof. exact (eq_refl m'). Qed.
Lemma lem7033144 (m : nat) (m' : nat) : (Nat.add m m') = (@I (nat -> nat -> nat) Nat.add m m').
Proof. exact (MK_COMB (@lem7033142 m) (@lem7033143 m')). Qed.
Lemma lem7033146 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033147 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7033146 nat nat f x). Qed.
Lemma lem7033148 (m : nat) (m' : nat) : (@I (nat -> nat -> nat) Nat.add m m') = (term513 m m').
Proof. exact (@lem7033147 (@I (nat -> nat -> nat) Nat.add m) m'). Qed.
Lemma lem7033150 (m : nat) (m' : nat) : (Nat.add m m') = (term513 m m').
Proof. exact (TRANS (@lem7033144 m m') (@lem7033148 m m')). Qed.
Lemma lem7033157 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033158 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7033157 nat (nat -> nat) f x). Qed.
Lemma lem7033159 (n : nat) : (Nat.add n) = (@I (nat -> nat -> nat) Nat.add n).
Proof. exact (@lem7033158 Nat.add n). Qed.
Lemma lem7033160 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem7033161 (n : nat) (n' : nat) : (Nat.add n n') = (@I (nat -> nat -> nat) Nat.add n n').
Proof. exact (MK_COMB (@lem7033159 n) (@lem7033160 n')). Qed.
Lemma lem7033163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033164 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7033163 nat nat f x). Qed.
Lemma lem7033165 (n : nat) (n' : nat) : (@I (nat -> nat -> nat) Nat.add n n') = (term513 n n').
Proof. exact (@lem7033164 (@I (nat -> nat -> nat) Nat.add n) n'). Qed.
Lemma lem7033167 (n : nat) (n' : nat) : (Nat.add n n') = (term513 n n').
Proof. exact (TRANS (@lem7033161 n n') (@lem7033165 n n')). Qed.
Lemma lem7033168 (R : type1605) (m : nat) (m' : nat) : (term514 R m m') = (term515 R m m').
Proof. exact (MK_COMB (@lem7033133 R) (@lem7033150 m m')). Qed.
Lemma lem7033169 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term32 R m m' n n') = (term516 R m m' n n').
Proof. exact (MK_COMB (@lem7033168 R m m') (@lem7033167 n n')). Qed.
Lemma lem7033171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033172 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033171 nat (nat -> Prop) f x). Qed.
Lemma lem7033173 (R : type1605) (m : nat) (m' : nat) : (term515 R m m') = (term517 R m m').
Proof. exact (@lem7033172 R (term513 m m')). Qed.
Lemma lem7033174 (n : nat) (n' : nat) : (term513 n n') = (term513 n n').
Proof. exact (eq_refl (term513 n n')). Qed.
Lemma lem7033175 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term516 R m m' n n') = (term518 R m m' n n').
Proof. exact (MK_COMB (@lem7033173 R m m') (@lem7033174 n n')). Qed.
Lemma lem7033177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033178 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033177 nat Prop f x). Qed.
Lemma lem7033179 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term518 R m m' n n') = (term519 R m m' n n').
Proof. exact (@lem7033178 (term517 R m m') (term513 n n')). Qed.
Lemma lem7033180 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term516 R m m' n n') = (term519 R m m' n n').
Proof. exact (TRANS (@lem7033175 R m m' n n') (@lem7033179 R m m' n n')). Qed.
Lemma lem7033181 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term32 R m m' n n') = (term519 R m m' n n').
Proof. exact (TRANS (@lem7033169 R m m' n n') (@lem7033180 R m m' n n')). Qed.
Lemma lem7033182 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7033189 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033190 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033189 nat (nat -> Prop) f x). Qed.
Lemma lem7033191 (R : type1605) (m' : nat) : (R m') = (@I (nat -> nat -> Prop) R m').
Proof. exact (@lem7033190 R m'). Qed.
Lemma lem7033192 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem7033193 (R : type1605) (m' : nat) (n' : nat) : (R m' n') = (@I (nat -> nat -> Prop) R m' n').
Proof. exact (MK_COMB (@lem7033191 R m') (@lem7033192 n')). Qed.
Lemma lem7033195 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033196 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033195 nat Prop f x). Qed.
Lemma lem7033197 (R : type1605) (m' : nat) (n' : nat) : (@I (nat -> nat -> Prop) R m' n') = (term520 R m' n').
Proof. exact (@lem7033196 (@I (nat -> nat -> Prop) R m') n'). Qed.
Lemma lem7033199 (R : type1605) (m' : nat) (n' : nat) : (R m' n') = (term520 R m' n').
Proof. exact (TRANS (@lem7033193 R m' n') (@lem7033197 R m' n')). Qed.
Lemma lem7033200 (R : type1605) (m' : nat) (n' : nat) : (term521 R m' n') = (term522 R m' n').
Proof. exact (MK_COMB (@lem7033182) (@lem7033199 R m' n')). Qed.
Lemma lem7033201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7033202 (R : type1605) (m' : nat) (n' : nat) : (term244 R m' n') = (term523 R m' n').
Proof. exact (MK_COMB (@lem7033201) (@lem7033200 R m' n')). Qed.
Lemma lem7033203 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term239 R m m' n n') = (term524 R m m' n n').
Proof. exact (MK_COMB (@lem7033202 R m' n') (@lem7033181 R m m' n n')). Qed.
Lemma lem7033204 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term240 R m m' n) = (term525 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7033203 R m m' n n')). Qed.
Lemma lem7033205 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033206 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term241 R m m' n) = (term526 R m m' n).
Proof. exact (MK_COMB (@lem7033205) (@lem7033204 R m m' n)). Qed.
Lemma lem7033207 (R : type1605) (m : nat) (n : nat) : (term242 R m n) = (term527 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7033206 R m m' n)). Qed.
Lemma lem7033208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033209 (R : type1605) (m : nat) (n : nat) : (term243 R m n) = (term528 R m n).
Proof. exact (MK_COMB (@lem7033208) (@lem7033207 R m n)). Qed.
Lemma lem7033210 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7033217 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033218 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033217 nat (nat -> Prop) f x). Qed.
Lemma lem7033219 (R : type1605) (m : nat) : (R m) = (@I (nat -> nat -> Prop) R m).
Proof. exact (@lem7033218 R m). Qed.
Lemma lem7033220 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7033221 (R : type1605) (m : nat) (n : nat) : (R m n) = (@I (nat -> nat -> Prop) R m n).
Proof. exact (MK_COMB (@lem7033219 R m) (@lem7033220 n)). Qed.
Lemma lem7033223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033224 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033223 nat Prop f x). Qed.
Lemma lem7033225 (R : type1605) (m : nat) (n : nat) : (@I (nat -> nat -> Prop) R m n) = (term520 R m n).
Proof. exact (@lem7033224 (@I (nat -> nat -> Prop) R m) n). Qed.
Lemma lem7033227 (R : type1605) (m : nat) (n : nat) : (R m n) = (term520 R m n).
Proof. exact (TRANS (@lem7033221 R m n) (@lem7033225 R m n)). Qed.
Lemma lem7033228 (R : type1605) (m : nat) (n : nat) : (term521 R m n) = (term522 R m n).
Proof. exact (MK_COMB (@lem7033210) (@lem7033227 R m n)). Qed.
Lemma lem7033229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7033230 (R : type1605) (m : nat) (n : nat) : (term244 R m n) = (term523 R m n).
Proof. exact (MK_COMB (@lem7033229) (@lem7033228 R m n)). Qed.
Lemma lem7033231 (R : type1605) (m : nat) (n : nat) : (term246 R m n) = (term529 R m n).
Proof. exact (MK_COMB (@lem7033230 R m n) (@lem7033209 R m n)). Qed.
Lemma lem7033232 (R : type1605) (m : nat) : (term247 R m) = (term530 R m).
Proof. exact (fun_ext (fun n : nat => @lem7033231 R m n)). Qed.
Lemma lem7033233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033234 (R : type1605) (m : nat) : (term248 R m) = (term531 R m).
Proof. exact (MK_COMB (@lem7033233) (@lem7033232 R m)). Qed.
Lemma lem7033235 (R : type1605) : (term249 R) = (term532 R).
Proof. exact (fun_ext (fun m : nat => @lem7033234 R m)). Qed.
Lemma lem7033236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033237 (R : type1605) : (term250 R) = (term533 R).
Proof. exact (MK_COMB (@lem7033236) (@lem7033235 R)). Qed.
Lemma lem7033238 (R : type1605) (h1 : term75 R) : term533 R.
Proof. exact (EQ_MP (@lem7033237 R) (@lem7032464 R h1)). Qed.
Lemma lem7033243 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033244 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7033243 (A -> Prop) Prop f x). Qed.
Lemma lem7033246 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7033244 A (@FINITE A) s). Qed.
Lemma lem7033248 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7033253 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033255 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7033253 A nat f x). Qed.
Lemma lem7033260 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033261 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7033260 A nat f x). Qed.
Lemma lem7033263 {A : Type'} (g : A -> nat) (x : A) : (g x) = (@I (A -> nat) g x).
Proof. exact (@lem7033261 A g x). Qed.
Lemma lem7033264 {A : Type'} (R : type1605) (f : A -> nat) (x : A) : (term534 A R f x) = (term535 A R f x).
Proof. exact (MK_COMB (@lem7033248 R) (@lem7033255 A f x)). Qed.
Lemma lem7033265 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term286 A R f g x) = (term536 A R f g x).
Proof. exact (MK_COMB (@lem7033264 A R f x) (@lem7033263 A g x)). Qed.
Lemma lem7033267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033268 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033267 nat (nat -> Prop) f x). Qed.
Lemma lem7033269 {A : Type'} (R : type1605) (f : A -> nat) (x : A) : (term535 A R f x) = (term537 A R f x).
Proof. exact (@lem7033268 R (@I (A -> nat) f x)). Qed.
Lemma lem7033270 {A : Type'} (g : A -> nat) (x : A) : (@I (A -> nat) g x) = (@I (A -> nat) g x).
Proof. exact (eq_refl (@I (A -> nat) g x)). Qed.
Lemma lem7033271 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term536 A R f g x) = (term538 A R f g x).
Proof. exact (MK_COMB (@lem7033269 A R f x) (@lem7033270 A g x)). Qed.
Lemma lem7033273 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033274 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033273 nat Prop f x). Qed.
Lemma lem7033275 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term538 A R f g x) = (term539 A R f g x).
Proof. exact (@lem7033274 (term537 A R f x) (@I (A -> nat) g x)). Qed.
Lemma lem7033276 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term536 A R f g x) = (term539 A R f g x).
Proof. exact (TRANS (@lem7033271 A R f g x) (@lem7033275 A R f g x)). Qed.
Lemma lem7033277 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term286 A R f g x) = (term539 A R f g x).
Proof. exact (TRANS (@lem7033265 A R f g x) (@lem7033276 A R f g x)). Qed.
Lemma lem7033278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7033285 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033286 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7033285 A (type686 A) f x). Qed.
Lemma lem7033287 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7033286 A (@IN A) x). Qed.
Lemma lem7033288 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7033289 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7033287 A x) (@lem7033288 A s)). Qed.
Lemma lem7033291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033292 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7033291 (A -> Prop) Prop f x). Qed.
Lemma lem7033293 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term540 A x s).
Proof. exact (@lem7033292 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7033295 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term540 A x s).
Proof. exact (TRANS (@lem7033289 A x s) (@lem7033293 A x s)). Qed.
Lemma lem7033296 {A : Type'} (x : A) (s : A -> Prop) : (term541 A x s) = (term542 A x s).
Proof. exact (MK_COMB (@lem7033278) (@lem7033295 A x s)). Qed.
Lemma lem7033297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7033298 {A : Type'} (x : A) (s : A -> Prop) : (term543 A x s) = (term544 A x s).
Proof. exact (MK_COMB (@lem7033297) (@lem7033296 A x s)). Qed.
Lemma lem7033299 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term510 A s R f g x) = (term545 A s R f g x).
Proof. exact (MK_COMB (@lem7033298 A x s) (@lem7033277 A R f g x)). Qed.
Lemma lem7033300 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term511 A s R f g) = (term546 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7033299 A s R f g x)). Qed.
Lemma lem7033301 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7033302 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term512 A s R f g) = (term547 A s R f g).
Proof. exact (MK_COMB (@lem7033301 A) (@lem7033300 A s R f g)). Qed.
Lemma lem7033303 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term547 A s R f g.
Proof. exact (EQ_MP (@lem7033302 A s R f g) (@lem7033089 A s R f g h1)). Qed.
Lemma lem7033304 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7033305 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7033312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033313 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem7033312 (A -> Prop) (type705 A) f x). Qed.
Lemma lem7033314 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem7033313 A (@nsum A) s). Qed.
Lemma lem7033315 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7033316 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f).
Proof. exact (MK_COMB (@lem7033314 A s) (@lem7033315 A f)). Qed.
Lemma lem7033318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033319 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem7033318 (A -> nat) nat f x). Qed.
Lemma lem7033320 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f) = (term548 A s f).
Proof. exact (@lem7033319 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) f). Qed.
Lemma lem7033322 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (term548 A s f).
Proof. exact (TRANS (@lem7033316 A s f) (@lem7033320 A s f)). Qed.
Lemma lem7033329 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033330 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem7033329 (A -> Prop) (type705 A) f x). Qed.
Lemma lem7033331 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem7033330 A (@nsum A) s). Qed.
Lemma lem7033332 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7033333 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g).
Proof. exact (MK_COMB (@lem7033331 A s) (@lem7033332 A g)). Qed.
Lemma lem7033335 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033336 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem7033335 (A -> nat) nat f x). Qed.
Lemma lem7033337 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g) = (term548 A s g).
Proof. exact (@lem7033336 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) g). Qed.
Lemma lem7033339 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (term548 A s g).
Proof. exact (TRANS (@lem7033333 A s g) (@lem7033337 A s g)). Qed.
Lemma lem7033340 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term189 A R s f) = (term549 A R s f).
Proof. exact (MK_COMB (@lem7033305 R) (@lem7033322 A s f)). Qed.
Lemma lem7033341 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term550 A R f s g).
Proof. exact (MK_COMB (@lem7033340 A R s f) (@lem7033339 A s g)). Qed.
Lemma lem7033343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033344 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033343 nat (nat -> Prop) f x). Qed.
Lemma lem7033345 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term549 A R s f) = (term551 A R s f).
Proof. exact (@lem7033344 R (term548 A s f)). Qed.
Lemma lem7033346 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term548 A s g) = (term548 A s g).
Proof. exact (eq_refl (term548 A s g)). Qed.
Lemma lem7033347 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term550 A R f s g) = (term552 A R f s g).
Proof. exact (MK_COMB (@lem7033345 A R s f) (@lem7033346 A s g)). Qed.
Lemma lem7033349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033350 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033349 nat Prop f x). Qed.
Lemma lem7033351 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term552 A R f s g) = (term553 A R f s g).
Proof. exact (@lem7033350 (term551 A R s f) (term548 A s g)). Qed.
Lemma lem7033352 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term550 A R f s g) = (term553 A R f s g).
Proof. exact (TRANS (@lem7033347 A R f s g) (@lem7033351 A R f s g)). Qed.
Lemma lem7033353 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term553 A R f s g).
Proof. exact (TRANS (@lem7033341 A R f s g) (@lem7033352 A R f s g)). Qed.
Lemma lem7033354 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term238 A R f s g) = (term554 A R f s g).
Proof. exact (MK_COMB (@lem7033304) (@lem7033353 A R f s g)). Qed.
Lemma lem7033356 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7033363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033364 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem7033363 (A -> Prop) (type705 A) f x). Qed.
Lemma lem7033365 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem7033364 A (@nsum A) s). Qed.
Lemma lem7033366 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7033367 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f).
Proof. exact (MK_COMB (@lem7033365 A s) (@lem7033366 A f)). Qed.
Lemma lem7033369 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033370 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem7033369 (A -> nat) nat f x). Qed.
Lemma lem7033371 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f) = (term548 A s f).
Proof. exact (@lem7033370 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) f). Qed.
Lemma lem7033373 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (term548 A s f).
Proof. exact (TRANS (@lem7033367 A s f) (@lem7033371 A s f)). Qed.
Lemma lem7033380 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033381 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem7033380 (A -> Prop) (type705 A) f x). Qed.
Lemma lem7033382 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem7033381 A (@nsum A) s). Qed.
Lemma lem7033383 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7033384 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g).
Proof. exact (MK_COMB (@lem7033382 A s) (@lem7033383 A g)). Qed.
Lemma lem7033386 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033387 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem7033386 (A -> nat) nat f x). Qed.
Lemma lem7033388 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g) = (term548 A s g).
Proof. exact (@lem7033387 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) g). Qed.
Lemma lem7033390 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (term548 A s g).
Proof. exact (TRANS (@lem7033384 A s g) (@lem7033388 A s g)). Qed.
Lemma lem7033391 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term189 A R s f) = (term549 A R s f).
Proof. exact (MK_COMB (@lem7033356 R) (@lem7033373 A s f)). Qed.
Lemma lem7033392 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term550 A R f s g).
Proof. exact (MK_COMB (@lem7033391 A R s f) (@lem7033390 A s g)). Qed.
Lemma lem7033394 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033395 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033394 nat (nat -> Prop) f x). Qed.
Lemma lem7033396 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term549 A R s f) = (term551 A R s f).
Proof. exact (@lem7033395 R (term548 A s f)). Qed.
Lemma lem7033397 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term548 A s g) = (term548 A s g).
Proof. exact (eq_refl (term548 A s g)). Qed.
Lemma lem7033398 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term550 A R f s g) = (term552 A R f s g).
Proof. exact (MK_COMB (@lem7033396 A R s f) (@lem7033397 A s g)). Qed.
Lemma lem7033400 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033401 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033400 nat Prop f x). Qed.
Lemma lem7033402 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term552 A R f s g) = (term553 A R f s g).
Proof. exact (@lem7033401 (term551 A R s f) (term548 A s g)). Qed.
Lemma lem7033403 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term550 A R f s g) = (term553 A R f s g).
Proof. exact (TRANS (@lem7033398 A R f s g) (@lem7033402 A R f s g)). Qed.
Lemma lem7033404 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term553 A R f s g).
Proof. exact (TRANS (@lem7033392 A R f s g) (@lem7033403 A R f s g)). Qed.
Lemma lem7033405 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7033406 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7033407 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7033416 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033417 {A : Type'} (f : type695 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7033416 (A -> nat) (type694 A) f x). Qed.
Lemma lem7033418 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7033417 A x f). Qed.
Lemma lem7033419 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7033420 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7033418 A x f) (@lem7033419 A g)). Qed.
Lemma lem7033422 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033423 {A : Type'} (f : type694 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7033422 (A -> nat) (type684 A) f x). Qed.
Lemma lem7033424 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g) = (term555 A x f g).
Proof. exact (@lem7033423 A (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7033425 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (term555 A x f g).
Proof. exact (TRANS (@lem7033420 A x f g) (@lem7033424 A x f g)). Qed.
Lemma lem7033426 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7033427 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term556 A x f g s).
Proof. exact (MK_COMB (@lem7033425 A x f g) (@lem7033426 A s)). Qed.
Lemma lem7033429 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033430 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7033429 (A -> Prop) A f x). Qed.
Lemma lem7033431 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term556 A x f g s) = (term557 A x f g s).
Proof. exact (@lem7033430 A (term555 A x f g) s). Qed.
Lemma lem7033433 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term557 A x f g s).
Proof. exact (TRANS (@lem7033427 A x f g s) (@lem7033431 A x f g s)). Qed.
Lemma lem7033434 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term558 A x f g s) = (term559 A x f g s).
Proof. exact (MK_COMB (@lem7033407 A f) (@lem7033433 A x f g s)). Qed.
Lemma lem7033436 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033437 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7033436 A nat f x). Qed.
Lemma lem7033438 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term559 A x f g s) = (term560 A x f g s).
Proof. exact (@lem7033437 A f (term557 A x f g s)). Qed.
Lemma lem7033439 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term558 A x f g s) = (term560 A x f g s).
Proof. exact (TRANS (@lem7033434 A x f g s) (@lem7033438 A x f g s)). Qed.
Lemma lem7033440 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7033449 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033450 {A : Type'} (f : type695 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7033449 (A -> nat) (type694 A) f x). Qed.
Lemma lem7033451 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7033450 A x f). Qed.
Lemma lem7033452 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7033453 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7033451 A x f) (@lem7033452 A g)). Qed.
Lemma lem7033455 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033456 {A : Type'} (f : type694 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7033455 (A -> nat) (type684 A) f x). Qed.
Lemma lem7033457 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g) = (term555 A x f g).
Proof. exact (@lem7033456 A (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7033458 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (term555 A x f g).
Proof. exact (TRANS (@lem7033453 A x f g) (@lem7033457 A x f g)). Qed.
Lemma lem7033459 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7033460 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term556 A x f g s).
Proof. exact (MK_COMB (@lem7033458 A x f g) (@lem7033459 A s)). Qed.
Lemma lem7033462 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033463 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7033462 (A -> Prop) A f x). Qed.
Lemma lem7033464 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term556 A x f g s) = (term557 A x f g s).
Proof. exact (@lem7033463 A (term555 A x f g) s). Qed.
Lemma lem7033466 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term557 A x f g s).
Proof. exact (TRANS (@lem7033460 A x f g s) (@lem7033464 A x f g s)). Qed.
Lemma lem7033467 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term561 A x f g s) = (term562 A x f g s).
Proof. exact (MK_COMB (@lem7033440 A g) (@lem7033466 A x f g s)). Qed.
Lemma lem7033469 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033470 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7033469 A nat f x). Qed.
Lemma lem7033471 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term562 A x f g s) = (term563 A x f g s).
Proof. exact (@lem7033470 A g (term557 A x f g s)). Qed.
Lemma lem7033472 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term561 A x f g s) = (term563 A x f g s).
Proof. exact (TRANS (@lem7033467 A x f g s) (@lem7033471 A x f g s)). Qed.
Lemma lem7033473 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term564 A R x f g s) = (term565 A R x f g s).
Proof. exact (MK_COMB (@lem7033406 R) (@lem7033439 A x f g s)). Qed.
Lemma lem7033474 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term566 A R x f g s) = (term567 A R x f g s).
Proof. exact (MK_COMB (@lem7033473 A R x f g s) (@lem7033472 A x f g s)). Qed.
Lemma lem7033476 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033477 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033476 nat (nat -> Prop) f x). Qed.
Lemma lem7033478 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term565 A R x f g s) = (term568 A R x f g s).
Proof. exact (@lem7033477 R (term560 A x f g s)). Qed.
Lemma lem7033479 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term563 A x f g s) = (term563 A x f g s).
Proof. exact (eq_refl (term563 A x f g s)). Qed.
Lemma lem7033480 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term567 A R x f g s) = (term569 A R x f g s).
Proof. exact (MK_COMB (@lem7033478 A R x f g s) (@lem7033479 A x f g s)). Qed.
Lemma lem7033482 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033483 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033482 nat Prop f x). Qed.
Lemma lem7033484 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term569 A R x f g s) = (term570 A R x f g s).
Proof. exact (@lem7033483 (term568 A R x f g s) (term563 A x f g s)). Qed.
Lemma lem7033485 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term567 A R x f g s) = (term570 A R x f g s).
Proof. exact (TRANS (@lem7033480 A R x f g s) (@lem7033484 A R x f g s)). Qed.
Lemma lem7033486 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term566 A R x f g s) = (term570 A R x f g s).
Proof. exact (TRANS (@lem7033474 A R x f g s) (@lem7033485 A R x f g s)). Qed.
Lemma lem7033487 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term571 A R x f g s) = (term572 A R x f g s).
Proof. exact (MK_COMB (@lem7033405) (@lem7033486 A R x f g s)). Qed.
Lemma lem7033488 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7033497 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033498 {A : Type'} (f : type695 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7033497 (A -> nat) (type694 A) f x). Qed.
Lemma lem7033499 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7033498 A x f). Qed.
Lemma lem7033500 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7033501 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7033499 A x f) (@lem7033500 A g)). Qed.
Lemma lem7033503 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033504 {A : Type'} (f : type694 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7033503 (A -> nat) (type684 A) f x). Qed.
Lemma lem7033505 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g) = (term555 A x f g).
Proof. exact (@lem7033504 A (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7033506 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (term555 A x f g).
Proof. exact (TRANS (@lem7033501 A x f g) (@lem7033505 A x f g)). Qed.
Lemma lem7033507 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7033508 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term556 A x f g s).
Proof. exact (MK_COMB (@lem7033506 A x f g) (@lem7033507 A s)). Qed.
Lemma lem7033510 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033511 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7033510 (A -> Prop) A f x). Qed.
Lemma lem7033512 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term556 A x f g s) = (term557 A x f g s).
Proof. exact (@lem7033511 A (term555 A x f g) s). Qed.
Lemma lem7033514 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term557 A x f g s).
Proof. exact (TRANS (@lem7033508 A x f g s) (@lem7033512 A x f g s)). Qed.
Lemma lem7033515 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7033516 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term573 A x f g s) = (term574 A x f g s).
Proof. exact (MK_COMB (@lem7033488 A) (@lem7033514 A x f g s)). Qed.
Lemma lem7033517 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term575 A x f g s) = (term576 A x f g s).
Proof. exact (MK_COMB (@lem7033516 A x f g s) (@lem7033515 A s)). Qed.
Lemma lem7033519 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033520 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7033519 A (type686 A) f x). Qed.
Lemma lem7033521 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term574 A x f g s) = (term577 A x f g s).
Proof. exact (@lem7033520 A (@IN A) (term557 A x f g s)). Qed.
Lemma lem7033522 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7033523 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term576 A x f g s) = (term578 A x f g s).
Proof. exact (MK_COMB (@lem7033521 A x f g s) (@lem7033522 A s)). Qed.
Lemma lem7033525 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033526 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7033525 (A -> Prop) Prop f x). Qed.
Lemma lem7033527 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term578 A x f g s) = (term579 A x f g s).
Proof. exact (@lem7033526 A (term577 A x f g s) s). Qed.
Lemma lem7033528 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term576 A x f g s) = (term579 A x f g s).
Proof. exact (TRANS (@lem7033523 A x f g s) (@lem7033527 A x f g s)). Qed.
Lemma lem7033529 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term575 A x f g s) = (term579 A x f g s).
Proof. exact (TRANS (@lem7033517 A x f g s) (@lem7033528 A x f g s)). Qed.
Lemma lem7033530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7033531 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term580 A x f g s) = (term581 A x f g s).
Proof. exact (MK_COMB (@lem7033530) (@lem7033529 A x f g s)). Qed.
Lemma lem7033532 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term582 A R x f g s) = (term583 A R x f g s).
Proof. exact (MK_COMB (@lem7033531 A x f g s) (@lem7033487 A R x f g s)). Qed.
Lemma lem7033533 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7033538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033539 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7033538 (A -> Prop) Prop f x). Qed.
Lemma lem7033541 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7033539 A (@FINITE A) s). Qed.
Lemma lem7033542 {A : Type'} (s : A -> Prop) : (term318 A s) = (term584 A s).
Proof. exact (MK_COMB (@lem7033533) (@lem7033541 A s)). Qed.
Lemma lem7033543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7033544 {A : Type'} (s : A -> Prop) : (term296 A s) = (term585 A s).
Proof. exact (MK_COMB (@lem7033543) (@lem7033542 A s)). Qed.
Lemma lem7033545 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term586 A R x f g s) = (term587 A R x f g s).
Proof. exact (MK_COMB (@lem7033544 A s) (@lem7033532 A R x f g s)). Qed.
Lemma lem7033546 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7033547 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term588 A R x f g s) = (term589 A R x f g s).
Proof. exact (MK_COMB (@lem7033546) (@lem7033545 A R x f g s)). Qed.
Lemma lem7033548 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term590 A x R f s g) = (term591 A x R f s g).
Proof. exact (MK_COMB (@lem7033547 A R x f g s) (@lem7033404 A R f s g)). Qed.
Lemma lem7033549 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term592 A x R f g) = (term593 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7033548 A x R f s g)). Qed.
Lemma lem7033550 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7033551 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term594 A x R f g) = (term595 A x R f g).
Proof. exact (MK_COMB (@lem7033550 A) (@lem7033549 A x R f g)). Qed.
Lemma lem7033552 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term596 A x R f) = (term597 A x R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7033551 A x R f g)). Qed.
Lemma lem7033553 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7033554 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term417 A x R f) = (term598 A x R f).
Proof. exact (MK_COMB (@lem7033553 A) (@lem7033552 A x R f)). Qed.
Lemma lem7033555 {A : Type'} (x : type695 A) (R : type1605) : (term419 A x R) = (term599 A x R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7033554 A x R f)). Qed.
Lemma lem7033556 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7033557 {A : Type'} (x : type695 A) (R : type1605) : (term421 A x R) = (term600 A x R).
Proof. exact (MK_COMB (@lem7033556 A) (@lem7033555 A x R)). Qed.
Lemma lem7033558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7033559 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7033566 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033567 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7033566 nat (nat -> nat) f x). Qed.
Lemma lem7033568 (x1 : nat) : (Nat.add x1) = (@I (nat -> nat -> nat) Nat.add x1).
Proof. exact (@lem7033567 Nat.add x1). Qed.
Lemma lem7033569 (y1 : nat) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem7033570 (x1 : nat) (y1 : nat) : (Nat.add x1 y1) = (@I (nat -> nat -> nat) Nat.add x1 y1).
Proof. exact (MK_COMB (@lem7033568 x1) (@lem7033569 y1)). Qed.
Lemma lem7033572 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033573 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7033572 nat nat f x). Qed.
Lemma lem7033574 (x1 : nat) (y1 : nat) : (@I (nat -> nat -> nat) Nat.add x1 y1) = (term513 x1 y1).
Proof. exact (@lem7033573 (@I (nat -> nat -> nat) Nat.add x1) y1). Qed.
Lemma lem7033576 (x1 : nat) (y1 : nat) : (Nat.add x1 y1) = (term513 x1 y1).
Proof. exact (TRANS (@lem7033570 x1 y1) (@lem7033574 x1 y1)). Qed.
Lemma lem7033583 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033584 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7033583 nat (nat -> nat) f x). Qed.
Lemma lem7033585 (x2 : nat) : (Nat.add x2) = (@I (nat -> nat -> nat) Nat.add x2).
Proof. exact (@lem7033584 Nat.add x2). Qed.
Lemma lem7033586 (y2 : nat) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem7033587 (x2 : nat) (y2 : nat) : (Nat.add x2 y2) = (@I (nat -> nat -> nat) Nat.add x2 y2).
Proof. exact (MK_COMB (@lem7033585 x2) (@lem7033586 y2)). Qed.
Lemma lem7033589 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033590 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7033589 nat nat f x). Qed.
Lemma lem7033591 (x2 : nat) (y2 : nat) : (@I (nat -> nat -> nat) Nat.add x2 y2) = (term513 x2 y2).
Proof. exact (@lem7033590 (@I (nat -> nat -> nat) Nat.add x2) y2). Qed.
Lemma lem7033593 (x2 : nat) (y2 : nat) : (Nat.add x2 y2) = (term513 x2 y2).
Proof. exact (TRANS (@lem7033587 x2 y2) (@lem7033591 x2 y2)). Qed.
Lemma lem7033594 (R : type1605) (x1 : nat) (y1 : nat) : (term514 R x1 y1) = (term515 R x1 y1).
Proof. exact (MK_COMB (@lem7033559 R) (@lem7033576 x1 y1)). Qed.
Lemma lem7033595 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term32 R x1 y1 x2 y2) = (term516 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7033594 R x1 y1) (@lem7033593 x2 y2)). Qed.
Lemma lem7033597 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033598 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033597 nat (nat -> Prop) f x). Qed.
Lemma lem7033599 (R : type1605) (x1 : nat) (y1 : nat) : (term515 R x1 y1) = (term517 R x1 y1).
Proof. exact (@lem7033598 R (term513 x1 y1)). Qed.
Lemma lem7033600 (x2 : nat) (y2 : nat) : (term513 x2 y2) = (term513 x2 y2).
Proof. exact (eq_refl (term513 x2 y2)). Qed.
Lemma lem7033601 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term516 R x1 y1 x2 y2) = (term518 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7033599 R x1 y1) (@lem7033600 x2 y2)). Qed.
Lemma lem7033603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033604 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033603 nat Prop f x). Qed.
Lemma lem7033605 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term518 R x1 y1 x2 y2) = (term519 R x1 y1 x2 y2).
Proof. exact (@lem7033604 (term517 R x1 y1) (term513 x2 y2)). Qed.
Lemma lem7033606 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term516 R x1 y1 x2 y2) = (term519 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7033601 R x1 y1 x2 y2) (@lem7033605 R x1 y1 x2 y2)). Qed.
Lemma lem7033607 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term32 R x1 y1 x2 y2) = (term519 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7033595 R x1 y1 x2 y2) (@lem7033606 R x1 y1 x2 y2)). Qed.
Lemma lem7033608 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term601 R x1 y1 x2 y2) = (term602 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7033558) (@lem7033607 R x1 y1 x2 y2)). Qed.
Lemma lem7033615 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033616 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033615 nat (nat -> Prop) f x). Qed.
Lemma lem7033617 (R : type1605) (y1 : nat) : (R y1) = (@I (nat -> nat -> Prop) R y1).
Proof. exact (@lem7033616 R y1). Qed.
Lemma lem7033618 (y2 : nat) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem7033619 (R : type1605) (y1 : nat) (y2 : nat) : (R y1 y2) = (@I (nat -> nat -> Prop) R y1 y2).
Proof. exact (MK_COMB (@lem7033617 R y1) (@lem7033618 y2)). Qed.
Lemma lem7033621 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033622 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033621 nat Prop f x). Qed.
Lemma lem7033623 (R : type1605) (y1 : nat) (y2 : nat) : (@I (nat -> nat -> Prop) R y1 y2) = (term520 R y1 y2).
Proof. exact (@lem7033622 (@I (nat -> nat -> Prop) R y1) y2). Qed.
Lemma lem7033625 (R : type1605) (y1 : nat) (y2 : nat) : (R y1 y2) = (term520 R y1 y2).
Proof. exact (TRANS (@lem7033619 R y1 y2) (@lem7033623 R y1 y2)). Qed.
Lemma lem7033632 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033633 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7033632 nat (nat -> Prop) f x). Qed.
Lemma lem7033634 (R : type1605) (x1 : nat) : (R x1) = (@I (nat -> nat -> Prop) R x1).
Proof. exact (@lem7033633 R x1). Qed.
Lemma lem7033635 (x2 : nat) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem7033636 (R : type1605) (x1 : nat) (x2 : nat) : (R x1 x2) = (@I (nat -> nat -> Prop) R x1 x2).
Proof. exact (MK_COMB (@lem7033634 R x1) (@lem7033635 x2)). Qed.
Lemma lem7033638 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7033639 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7033638 nat Prop f x). Qed.
Lemma lem7033640 (R : type1605) (x1 : nat) (x2 : nat) : (@I (nat -> nat -> Prop) R x1 x2) = (term520 R x1 x2).
Proof. exact (@lem7033639 (@I (nat -> nat -> Prop) R x1) x2). Qed.
Lemma lem7033642 (R : type1605) (x1 : nat) (x2 : nat) : (R x1 x2) = (term520 R x1 x2).
Proof. exact (TRANS (@lem7033636 R x1 x2) (@lem7033640 R x1 x2)). Qed.
Lemma lem7033643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7033644 (R : type1605) (x1 : nat) (x2 : nat) : (term603 R x1 x2) = (term604 R x1 x2).
Proof. exact (MK_COMB (@lem7033643) (@lem7033642 R x1 x2)). Qed.
Lemma lem7033645 (x1 : nat) (x2 : nat) (R : type1605) (y1 : nat) (y2 : nat) : (term253 x1 x2 R y1 y2) = (term605 x1 x2 R y1 y2).
Proof. exact (MK_COMB (@lem7033644 R x1 x2) (@lem7033625 R y1 y2)). Qed.
Lemma lem7033646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7033647 (x1 : nat) (x2 : nat) (R : type1605) (y1 : nat) (y2 : nat) : (term606 x1 x2 R y1 y2) = (term607 x1 x2 R y1 y2).
Proof. exact (MK_COMB (@lem7033646) (@lem7033645 x1 x2 R y1 y2)). Qed.
Lemma lem7033648 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term252 R x1 y1 x2 y2) = (term608 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7033647 x1 x2 R y1 y2) (@lem7033608 R x1 y1 x2 y2)). Qed.
Lemma lem7033649 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7033650 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term482 R x1 y1 x2 y2) = (term609 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7033649) (@lem7033648 R x1 y1 x2 y2)). Qed.
Lemma lem7033651 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) : (term498 A x1 y1 x2 y2 x R) = (term610 A x1 y1 x2 y2 x R).
Proof. exact (MK_COMB (@lem7033650 R x1 y1 x2 y2) (@lem7033557 A x R)). Qed.
Lemma lem7033652 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) (h1 : term498 A x1 y1 x2 y2 x R) : term610 A x1 y1 x2 y2 x R.
Proof. exact (EQ_MP (@lem7033651 A x1 y1 x2 y2 x R) (@lem7033100 A x1 y1 x2 y2 x R h1)). Qed.
Lemma lem7033653 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term608 R x1 y1 x2 y2.
Proof. exact (h1). Qed.
Lemma lem7033654 {A : Type'} (x : type695 A) (R : type1605) (h1 : term600 A x R) : term600 A x R.
Proof. exact (h1). Qed.
Lemma lem7033656 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term605 x1 x2 R y1 y2.
Proof. exact (proj1 (@lem7033653 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7033664 {A : Type'} (P : Prop) (Q : A -> Prop) : (term611 A P Q) = (term612 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7033665 (P : Prop) (Q : nat -> Prop) : (term613 P Q) = (term614 P Q).
Proof. exact (@lem7033664 nat P Q). Qed.
Lemma lem7033666 (R : type1605) (m : nat) (n : nat) : (term615 R m n) = (term616 R m n).
Proof. exact (@lem7033665 (term522 R m n) (term527 R m n)). Qed.
Lemma lem7033667 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term617 R m n m') = (term526 R m m' n).
Proof. exact (eq_refl (term617 R m n m')). Qed.
Lemma lem7033668 (R : type1605) (m : nat) (n : nat) : (term618 R m n) = (term527 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7033667 R m m' n)). Qed.
Lemma lem7033669 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033670 (R : type1605) (m : nat) (n : nat) : (term619 R m n) = (term528 R m n).
Proof. exact (MK_COMB (@lem7033669) (@lem7033668 R m n)). Qed.
Lemma lem7033671 (R : type1605) (m : nat) (n : nat) : (term523 R m n) = (term523 R m n).
Proof. exact (eq_refl (term523 R m n)). Qed.
Lemma lem7033672 (R : type1605) (m : nat) (n : nat) : (term615 R m n) = (term529 R m n).
Proof. exact (MK_COMB (@lem7033671 R m n) (@lem7033670 R m n)). Qed.
Lemma lem7033673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7033674 (R : type1605) (m : nat) (n : nat) : (term620 R m n) = (term621 R m n).
Proof. exact (MK_COMB (@lem7033673) (@lem7033672 R m n)). Qed.
Lemma lem7033675 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term617 R m n m') = (term526 R m m' n).
Proof. exact (eq_refl (term617 R m n m')). Qed.
Lemma lem7033676 (R : type1605) (m : nat) (n : nat) : (term523 R m n) = (term523 R m n).
Proof. exact (eq_refl (term523 R m n)). Qed.
Lemma lem7033677 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term622 R m n m') = (term623 R m m' n).
Proof. exact (MK_COMB (@lem7033676 R m n) (@lem7033675 R m m' n)). Qed.
Lemma lem7033678 (R : type1605) (m : nat) (n : nat) : (term624 R m n) = (term625 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7033677 R m m' n)). Qed.
Lemma lem7033679 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033680 (R : type1605) (m : nat) (n : nat) : (term616 R m n) = (term626 R m n).
Proof. exact (MK_COMB (@lem7033679) (@lem7033678 R m n)). Qed.
Lemma lem7033681 (R : type1605) (m : nat) (n : nat) : ((term615 R m n) = (term616 R m n)) = ((term529 R m n) = (term626 R m n)).
Proof. exact (MK_COMB (@lem7033674 R m n) (@lem7033680 R m n)). Qed.
Lemma lem7033682 (R : type1605) (m : nat) (n : nat) : (term529 R m n) = (term626 R m n).
Proof. exact (EQ_MP (@lem7033681 R m n) (@lem7033666 R m n)). Qed.
Lemma lem7033684 {A : Type'} (P : Prop) (Q : A -> Prop) : (term611 A P Q) = (term612 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7033685 (P : Prop) (Q : nat -> Prop) : (term613 P Q) = (term614 P Q).
Proof. exact (@lem7033684 nat P Q). Qed.
Lemma lem7033686 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term627 R m m' n) = (term628 R m m' n).
Proof. exact (@lem7033685 (term522 R m n) (term525 R m m' n)). Qed.
Lemma lem7033687 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term629 R m m' n n') = (term524 R m m' n n').
Proof. exact (eq_refl (term629 R m m' n n')). Qed.
Lemma lem7033688 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term630 R m m' n) = (term525 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7033687 R m m' n n')). Qed.
Lemma lem7033689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033690 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term631 R m m' n) = (term526 R m m' n).
Proof. exact (MK_COMB (@lem7033689) (@lem7033688 R m m' n)). Qed.
Lemma lem7033691 (R : type1605) (m : nat) (n : nat) : (term523 R m n) = (term523 R m n).
Proof. exact (eq_refl (term523 R m n)). Qed.
Lemma lem7033692 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term627 R m m' n) = (term623 R m m' n).
Proof. exact (MK_COMB (@lem7033691 R m n) (@lem7033690 R m m' n)). Qed.
Lemma lem7033693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7033694 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term632 R m m' n) = (term633 R m m' n).
Proof. exact (MK_COMB (@lem7033693) (@lem7033692 R m m' n)). Qed.
Lemma lem7033695 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term629 R m m' n n') = (term524 R m m' n n').
Proof. exact (eq_refl (term629 R m m' n n')). Qed.
Lemma lem7033696 (R : type1605) (m : nat) (n : nat) : (term523 R m n) = (term523 R m n).
Proof. exact (eq_refl (term523 R m n)). Qed.
Lemma lem7033697 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term634 R m m' n n') = (term635 R m m' n n').
Proof. exact (MK_COMB (@lem7033696 R m n) (@lem7033695 R m m' n n')). Qed.
Lemma lem7033698 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term636 R m m' n) = (term637 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7033697 R m m' n n')). Qed.
Lemma lem7033699 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033700 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term628 R m m' n) = (term638 R m m' n).
Proof. exact (MK_COMB (@lem7033699) (@lem7033698 R m m' n)). Qed.
Lemma lem7033701 (R : type1605) (m : nat) (m' : nat) (n : nat) : ((term627 R m m' n) = (term628 R m m' n)) = ((term623 R m m' n) = (term638 R m m' n)).
Proof. exact (MK_COMB (@lem7033694 R m m' n) (@lem7033700 R m m' n)). Qed.
Lemma lem7033702 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term623 R m m' n) = (term638 R m m' n).
Proof. exact (EQ_MP (@lem7033701 R m m' n) (@lem7033686 R m m' n)). Qed.
Lemma lem7033703 (R : type1605) (m : nat) (n : nat) : (term625 R m n) = (term639 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7033702 R m m' n)). Qed.
Lemma lem7033704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033705 (R : type1605) (m : nat) (n : nat) : (term626 R m n) = (term640 R m n).
Proof. exact (MK_COMB (@lem7033704) (@lem7033703 R m n)). Qed.
Lemma lem7033706 (R : type1605) (m : nat) (n : nat) : (term529 R m n) = (term640 R m n).
Proof. exact (TRANS (@lem7033682 R m n) (@lem7033705 R m n)). Qed.
Lemma lem7033707 (R : type1605) (m : nat) : (term530 R m) = (term641 R m).
Proof. exact (fun_ext (fun n : nat => @lem7033706 R m n)). Qed.
Lemma lem7033708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033709 (R : type1605) (m : nat) : (term531 R m) = (term642 R m).
Proof. exact (MK_COMB (@lem7033708) (@lem7033707 R m)). Qed.
Lemma lem7033710 (R : type1605) : (term532 R) = (term643 R).
Proof. exact (fun_ext (fun m : nat => @lem7033709 R m)). Qed.
Lemma lem7033711 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033712 (R : type1605) : (term533 R) = (term644 R).
Proof. exact (MK_COMB (@lem7033711) (@lem7033710 R)). Qed.
Lemma lem7033725 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term635 R m m' n n') = (term635 R m m' n n').
Proof. exact (eq_refl (term635 R m m' n n')). Qed.
Lemma lem7033726 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term637 R m m' n) = (term637 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7033725 R m m' n n')). Qed.
Lemma lem7033727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033728 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term638 R m m' n) = (term638 R m m' n).
Proof. exact (MK_COMB (@lem7033727) (@lem7033726 R m m' n)). Qed.
Lemma lem7033729 (R : type1605) (m : nat) (n : nat) : (term639 R m n) = (term639 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7033728 R m m' n)). Qed.
Lemma lem7033730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033731 (R : type1605) (m : nat) (n : nat) : (term640 R m n) = (term640 R m n).
Proof. exact (MK_COMB (@lem7033730) (@lem7033729 R m n)). Qed.
Lemma lem7033732 (R : type1605) (m : nat) : (term641 R m) = (term641 R m).
Proof. exact (fun_ext (fun n : nat => @lem7033731 R m n)). Qed.
Lemma lem7033733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033734 (R : type1605) (m : nat) : (term642 R m) = (term642 R m).
Proof. exact (MK_COMB (@lem7033733) (@lem7033732 R m)). Qed.
Lemma lem7033735 (R : type1605) : (term643 R) = (term643 R).
Proof. exact (fun_ext (fun m : nat => @lem7033734 R m)). Qed.
Lemma lem7033736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7033737 (R : type1605) : (term644 R) = (term644 R).
Proof. exact (MK_COMB (@lem7033736) (@lem7033735 R)). Qed.
Lemma lem7033738 (R : type1605) : (term533 R) = (term644 R).
Proof. exact (TRANS (@lem7033712 R) (@lem7033737 R)). Qed.
Lemma lem7033739 (R : type1605) (h1 : term75 R) : term644 R.
Proof. exact (EQ_MP (@lem7033738 R) (@lem7033238 R h1)). Qed.
Lemma lem7033865 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term545 A s R f g x) = (term545 A s R f g x).
Proof. exact (eq_refl (term545 A s R f g x)). Qed.
Lemma lem7033866 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term546 A s R f g) = (term546 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7033865 A s R f g x)). Qed.
Lemma lem7033867 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7033869 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term547 A s R f g) = (term547 A s R f g).
Proof. exact (MK_COMB (@lem7033867 A) (@lem7033866 A s R f g)). Qed.
Lemma lem7033870 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term547 A s R f g.
Proof. exact (EQ_MP (@lem7033869 A s R f g) (@lem7033303 A s R f g h1)). Qed.
Lemma lem7033876 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term553 A R f s g) = (term553 A R f s g).
Proof. exact (eq_refl (term553 A R f s g)). Qed.
Lemma lem7033893 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term587 A R x f g s) = (term645 A R x f g s).
Proof. exact (@lem19490 (term579 A x f g s) (term584 A s) (term572 A R x f g s)). Qed.
Lemma lem7033894 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7033895 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term589 A R x f g s) = (term646 A R x f g s).
Proof. exact (MK_COMB (@lem7033894) (@lem7033893 A R x f g s)). Qed.
Lemma lem7033896 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term591 A x R f s g) = (term647 A x R f s g).
Proof. exact (MK_COMB (@lem7033895 A R x f g s) (@lem7033876 A R f s g)). Qed.
Lemma lem7033903 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term647 A x R f s g) = (term648 A x R f s g).
Proof. exact (@lem19699 (term649 A x f g s) (term650 A R x f g s) (term553 A R f s g)). Qed.
Lemma lem7033904 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term591 A x R f s g) = (term648 A x R f s g).
Proof. exact (TRANS (@lem7033896 A x R f s g) (@lem7033903 A x R f s g)). Qed.
Lemma lem7033905 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term593 A x R f g) = (term651 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7033904 A x R f s g)). Qed.
Lemma lem7033906 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7033907 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term595 A x R f g) = (term652 A x R f g).
Proof. exact (MK_COMB (@lem7033906 A) (@lem7033905 A x R f g)). Qed.
Lemma lem7033908 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term597 A x R f) = (term653 A x R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7033907 A x R f g)). Qed.
Lemma lem7033909 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7033910 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term598 A x R f) = (term654 A x R f).
Proof. exact (MK_COMB (@lem7033909 A) (@lem7033908 A x R f)). Qed.
Lemma lem7033911 {A : Type'} (x : type695 A) (R : type1605) : (term599 A x R) = (term655 A x R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7033910 A x R f)). Qed.
Lemma lem7033912 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7033914 {A : Type'} (x : type695 A) (R : type1605) : (term600 A x R) = (term656 A x R).
Proof. exact (MK_COMB (@lem7033912 A) (@lem7033911 A x R)). Qed.
Lemma lem7033915 {A : Type'} (x : type695 A) (R : type1605) (h1 : term600 A x R) : term656 A x R.
Proof. exact (EQ_MP (@lem7033914 A x R) (@lem7033654 A x R h1)). Qed.
Lemma lem7033916 (_93889 : nat) (R : type1605) (h1 : term75 R) : term657 R _93889.
Proof. exact (@lem7033739 R h1 _93889). Qed.
Lemma lem7033917 (R : type1605) (_93889 : nat) : (term657 R _93889) = (term642 R _93889).
Proof. exact (eq_refl (term657 R _93889)). Qed.
Lemma lem7033918 (_93889 : nat) (R : type1605) (h1 : term75 R) : term642 R _93889.
Proof. exact (EQ_MP (@lem7033917 R _93889) (@lem7033916 _93889 R h1)). Qed.
Lemma lem7033919 (_93889 : nat) (_93890 : nat) (R : type1605) (h1 : term75 R) : term658 R _93889 _93890.
Proof. exact (@lem7033918 _93889 R h1 _93890). Qed.
Lemma lem7033920 (R : type1605) (_93889 : nat) (_93890 : nat) : (term658 R _93889 _93890) = (term640 R _93889 _93890).
Proof. exact (eq_refl (term658 R _93889 _93890)). Qed.
Lemma lem7033921 (_93889 : nat) (_93890 : nat) (R : type1605) (h1 : term75 R) : term640 R _93889 _93890.
Proof. exact (EQ_MP (@lem7033920 R _93889 _93890) (@lem7033919 _93889 _93890 R h1)). Qed.
Lemma lem7033922 (_93889 : nat) (_93890 : nat) (_93891 : nat) (R : type1605) (h1 : term75 R) : term659 R _93889 _93890 _93891.
Proof. exact (@lem7033921 _93889 _93890 R h1 _93891). Qed.
Lemma lem7033923 (R : type1605) (_93889 : nat) (_93891 : nat) (_93890 : nat) : (term659 R _93889 _93890 _93891) = (term638 R _93889 _93891 _93890).
Proof. exact (eq_refl (term659 R _93889 _93890 _93891)). Qed.
Lemma lem7033924 (_93889 : nat) (_93891 : nat) (_93890 : nat) (R : type1605) (h1 : term75 R) : term638 R _93889 _93891 _93890.
Proof. exact (EQ_MP (@lem7033923 R _93889 _93891 _93890) (@lem7033922 _93889 _93890 _93891 R h1)). Qed.
Lemma lem7033925 (_93889 : nat) (_93891 : nat) (_93890 : nat) (_93892 : nat) (R : type1605) (h1 : term75 R) : term660 R _93889 _93891 _93890 _93892.
Proof. exact (@lem7033924 _93889 _93891 _93890 R h1 _93892). Qed.
Lemma lem7033926 (R : type1605) (_93889 : nat) (_93891 : nat) (_93890 : nat) (_93892 : nat) : (term660 R _93889 _93891 _93890 _93892) = (term635 R _93889 _93891 _93890 _93892).
Proof. exact (eq_refl (term660 R _93889 _93891 _93890 _93892)). Qed.
Lemma lem7033943 {A : Type'} (_93898 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term661 A s R f g _93898.
Proof. exact (@lem7033870 A s R f g h1 _93898). Qed.
Lemma lem7033944 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) : (term661 A s R f g _93898) = (term545 A s R f g _93898).
Proof. exact (eq_refl (term661 A s R f g _93898)). Qed.
Lemma lem7033946 {A : Type'} (_93899 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term662 A x R _93899.
Proof. exact (@lem7033915 A x R h1 _93899). Qed.
Lemma lem7033947 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) : (term662 A x R _93899) = (term654 A x R _93899).
Proof. exact (eq_refl (term662 A x R _93899)). Qed.
Lemma lem7033948 {A : Type'} (_93899 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term654 A x R _93899.
Proof. exact (EQ_MP (@lem7033947 A x R _93899) (@lem7033946 A _93899 x R h1)). Qed.
Lemma lem7033949 {A : Type'} (_93899 : A -> nat) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term663 A x R _93899 _93900.
Proof. exact (@lem7033948 A _93899 x R h1 _93900). Qed.
Lemma lem7033950 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93900 : A -> nat) : (term663 A x R _93899 _93900) = (term652 A x R _93899 _93900).
Proof. exact (eq_refl (term663 A x R _93899 _93900)). Qed.
Lemma lem7033951 {A : Type'} (_93899 : A -> nat) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term652 A x R _93899 _93900.
Proof. exact (EQ_MP (@lem7033950 A x R _93899 _93900) (@lem7033949 A _93899 _93900 x R h1)). Qed.
Lemma lem7033952 {A : Type'} (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term664 A x R _93899 _93900 _93901.
Proof. exact (@lem7033951 A _93899 _93900 x R h1 _93901). Qed.
Lemma lem7033953 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term664 A x R _93899 _93900 _93901) = (term648 A x R _93899 _93901 _93900).
Proof. exact (eq_refl (term664 A x R _93899 _93900 _93901)). Qed.
Lemma lem7033954 {A : Type'} (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term648 A x R _93899 _93901 _93900.
Proof. exact (EQ_MP (@lem7033953 A x R _93899 _93901 _93900) (@lem7033952 A _93899 _93900 _93901 x R h1)). Qed.
Lemma lem7033955 {A : Type'} (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term665 A x R _93899 _93901 _93900.
Proof. exact (proj2 (@lem7033954 A _93899 _93901 _93900 x R h1)). Qed.
Lemma lem7033956 {A : Type'} (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term666 A x R _93899 _93901 _93900.
Proof. exact (proj1 (@lem7033954 A _93899 _93901 _93900 x R h1)). Qed.
Lemma lem7033968 (_93889 : nat) (_93891 : nat) (_93890 : nat) (_93892 : nat) (R : type1605) (h1 : term75 R) : term635 R _93889 _93891 _93890 _93892.
Proof. exact (EQ_MP (@lem7033926 R _93889 _93891 _93890 _93892) (@lem7033925 _93889 _93891 _93890 _93892 R h1)). Qed.
Lemma lem7033980 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term602 R x1 y1 x2 y2.
Proof. exact (proj2 (@lem7033653 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7034004 {A : Type'} (_93898 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term545 A s R f g _93898.
Proof. exact (EQ_MP (@lem7033944 A s R f g _93898) (@lem7033943 A _93898 s R f g h1)). Qed.
Lemma lem7034006 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term238 A R f s g) : term554 A R f s g.
Proof. exact (EQ_MP (@lem7033354 A R f s g) (@lem7033095 A R f s g h1)). Qed.
Lemma lem7034017 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term666 A x R _93899 _93901 _93900) = (term667 A x R _93899 _93901 _93900).
Proof. exact (@lem7030916 (term584 A _93901) (term579 A x _93899 _93900 _93901) (term553 A R _93899 _93901 _93900)). Qed.
Lemma lem7034018 {A : Type'} (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term667 A x R _93899 _93901 _93900.
Proof. exact (EQ_MP (@lem7034017 A x R _93899 _93901 _93900) (@lem7033956 A _93899 _93901 _93900 x R h1)). Qed.
Lemma lem7034029 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term665 A x R _93899 _93901 _93900) = (term668 A x R _93899 _93901 _93900).
Proof. exact (@lem7030916 (term584 A _93901) (term572 A R x _93899 _93900 _93901) (term553 A R _93899 _93901 _93900)). Qed.
Lemma lem7034030 {A : Type'} (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term668 A x R _93899 _93901 _93900.
Proof. exact (EQ_MP (@lem7034029 A x R _93899 _93901 _93900) (@lem7033955 A _93899 _93901 _93900 x R h1)). Qed.
Lemma lem7034032 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term520 R x1 x2.
Proof. exact (proj1 (@lem7033656 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7034033 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term669 R x1 x2.
Proof. exact (fun h0 : term522 R x1 x2 => @lem7034032 R x1 y1 x2 y2 h1). Qed.
Lemma lem7034035 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034036 (R : type1605) (x1 : nat) (x2 : nat) : (term669 R x1 x2) = (term520 R x1 x2).
Proof. exact (@lem7034035 (term520 R x1 x2)). Qed.
Lemma lem7034037 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term520 R x1 x2.
Proof. exact (EQ_MP (@lem7034036 R x1 x2) (@lem7034033 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7034039 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term520 R y1 y2.
Proof. exact (proj2 (@lem7033656 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7034040 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term669 R y1 y2.
Proof. exact (fun h0 : term522 R y1 y2 => @lem7034039 R x1 y1 x2 y2 h1). Qed.
Lemma lem7034042 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034043 (R : type1605) (y1 : nat) (y2 : nat) : (term669 R y1 y2) = (term520 R y1 y2).
Proof. exact (@lem7034042 (term520 R y1 y2)). Qed.
Lemma lem7034044 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term520 R y1 y2.
Proof. exact (EQ_MP (@lem7034043 R y1 y2) (@lem7034040 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7034060 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7034061 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term524 R _93889 _93891 _93890 _93892) = (term671 _93889 _93890 R _93891 _93892).
Proof. exact (@lem7034060 (term519 R _93889 _93891 _93890 _93892) (term522 R _93891 _93892)). Qed.
Lemma lem7034067 (R : type1605) (_93889 : nat) (_93890 : nat) : (term523 R _93889 _93890) = (term523 R _93889 _93890).
Proof. exact (eq_refl (term523 R _93889 _93890)). Qed.
Lemma lem7034068 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term635 R _93889 _93891 _93890 _93892) = (term672 _93889 _93890 R _93891 _93892).
Proof. exact (MK_COMB (@lem7034067 R _93889 _93890) (@lem7034061 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034072 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7034073 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term672 _93889 _93890 R _93891 _93892) = (term673 _93889 _93890 R _93891 _93892).
Proof. exact (@lem7034072 (term519 R _93889 _93891 _93890 _93892) (term522 R _93889 _93890) (term522 R _93891 _93892)). Qed.
Lemma lem7034089 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term635 R _93889 _93891 _93890 _93892) = (term673 _93889 _93890 R _93891 _93892).
Proof. exact (TRANS (@lem7034068 _93889 _93890 R _93891 _93892) (@lem7034073 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7034091 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term674 R _93889 _93891 _93890 _93892) = (term675 _93889 _93890 R _93891 _93892).
Proof. exact (MK_COMB (@lem7034090) (@lem7034089 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034107 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term673 _93889 _93890 R _93891 _93892) = (term673 _93889 _93890 R _93891 _93892).
Proof. exact (eq_refl (term673 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034108 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : ((term635 R _93889 _93891 _93890 _93892) = (term673 _93889 _93890 R _93891 _93892)) = ((term673 _93889 _93890 R _93891 _93892) = (term673 _93889 _93890 R _93891 _93892)).
Proof. exact (MK_COMB (@lem7034091 _93889 _93890 R _93891 _93892) (@lem7034107 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034110 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7034111 (x : Prop) : (x = x) = True.
Proof. exact (@lem7034110 Prop x). Qed.
Lemma lem7034112 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : ((term673 _93889 _93890 R _93891 _93892) = (term673 _93889 _93890 R _93891 _93892)) = True.
Proof. exact (@lem7034111 (term673 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034113 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : ((term635 R _93889 _93891 _93890 _93892) = (term673 _93889 _93890 R _93891 _93892)) = True.
Proof. exact (TRANS (@lem7034108 _93889 _93890 R _93891 _93892) (@lem7034112 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034114 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : True = ((term635 R _93889 _93891 _93890 _93892) = (term673 _93889 _93890 R _93891 _93892)).
Proof. exact (SYM (@lem7034113 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034115 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term635 R _93889 _93891 _93890 _93892) = (term673 _93889 _93890 R _93891 _93892).
Proof. exact (EQ_MP (@lem7034114 _93889 _93890 R _93891 _93892) (@lem0)). Qed.
Lemma lem7034116 (_93889 : nat) (_93890 : nat) (_93891 : nat) (_93892 : nat) (R : type1605) (h1 : term75 R) : term673 _93889 _93890 R _93891 _93892.
Proof. exact (EQ_MP (@lem7034115 _93889 _93890 R _93891 _93892) (@lem7033968 _93889 _93891 _93890 _93892 R h1)). Qed.
Lemma lem7034118 (b : Prop) (a : Prop) : (a \/ b) = (term676 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7034119 (R : type1605) (_93889 : nat) (_93891 : nat) (_93890 : nat) (_93892 : nat) : (term673 _93889 _93890 R _93891 _93892) = (term677 R _93889 _93891 _93890 _93892).
Proof. exact (@lem7034118 (term678 _93889 _93890 R _93891 _93892) (term519 R _93889 _93891 _93890 _93892)). Qed.
Lemma lem7034121 (a : Prop) (b : Prop) : (term679 a b) = (term680 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7034122 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term681 _93889 _93890 R _93891 _93892) = (term682 _93889 _93890 R _93891 _93892).
Proof. exact (@lem7034121 (term522 R _93889 _93890) (term522 R _93891 _93892)). Qed.
Lemma lem7034124 (a : Prop) : (term218 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7034125 (R : type1605) (_93889 : nat) (_93890 : nat) : (term683 R _93889 _93890) = (term520 R _93889 _93890).
Proof. exact (@lem7034124 (term520 R _93889 _93890)). Qed.
Lemma lem7034126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7034127 (R : type1605) (_93889 : nat) (_93890 : nat) : (term684 R _93889 _93890) = (term604 R _93889 _93890).
Proof. exact (MK_COMB (@lem7034126) (@lem7034125 R _93889 _93890)). Qed.
Lemma lem7034129 (a : Prop) : (term218 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7034130 (R : type1605) (_93891 : nat) (_93892 : nat) : (term683 R _93891 _93892) = (term520 R _93891 _93892).
Proof. exact (@lem7034129 (term520 R _93891 _93892)). Qed.
Lemma lem7034131 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term682 _93889 _93890 R _93891 _93892) = (term605 _93889 _93890 R _93891 _93892).
Proof. exact (MK_COMB (@lem7034127 R _93889 _93890) (@lem7034130 R _93891 _93892)). Qed.
Lemma lem7034132 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term681 _93889 _93890 R _93891 _93892) = (term605 _93889 _93890 R _93891 _93892).
Proof. exact (TRANS (@lem7034122 _93889 _93890 R _93891 _93892) (@lem7034131 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034133 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7034134 (_93889 : nat) (_93890 : nat) (R : type1605) (_93891 : nat) (_93892 : nat) : (term685 _93889 _93890 R _93891 _93892) = (term686 _93889 _93890 R _93891 _93892).
Proof. exact (MK_COMB (@lem7034133) (@lem7034132 _93889 _93890 R _93891 _93892)). Qed.
Lemma lem7034135 (R : type1605) (_93889 : nat) (_93891 : nat) (_93890 : nat) (_93892 : nat) : (term519 R _93889 _93891 _93890 _93892) = (term519 R _93889 _93891 _93890 _93892).
Proof. exact (eq_refl (term519 R _93889 _93891 _93890 _93892)). Qed.
Lemma lem7034136 (R : type1605) (_93889 : nat) (_93891 : nat) (_93890 : nat) (_93892 : nat) : (term677 R _93889 _93891 _93890 _93892) = (term687 R _93889 _93891 _93890 _93892).
Proof. exact (MK_COMB (@lem7034134 _93889 _93890 R _93891 _93892) (@lem7034135 R _93889 _93891 _93890 _93892)). Qed.
Lemma lem7034137 (R : type1605) (_93889 : nat) (_93891 : nat) (_93890 : nat) (_93892 : nat) : (term673 _93889 _93890 R _93891 _93892) = (term687 R _93889 _93891 _93890 _93892).
Proof. exact (TRANS (@lem7034119 R _93889 _93891 _93890 _93892) (@lem7034136 R _93889 _93891 _93890 _93892)). Qed.
Lemma lem7034139 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term605 x1 x2 R y1 y2.
Proof. exact (conj (@lem7034037 R x1 y1 x2 y2 h1) (@lem7034044 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7034141 (_93889 : nat) (_93891 : nat) (_93890 : nat) (_93892 : nat) (R : type1605) (h1 : term75 R) : term687 R _93889 _93891 _93890 _93892.
Proof. exact (EQ_MP (@lem7034137 R _93889 _93891 _93890 _93892) (@lem7034116 _93889 _93890 _93891 _93892 R h1)). Qed.
Lemma lem7034142 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) (h1 : term75 R) : term687 R x1 y1 x2 y2.
Proof. exact (@lem7034141 x1 y1 x2 y2 R h1). Qed.
Lemma lem7034145 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term75 R) (h2 : term608 R x1 y1 x2 y2) : term519 R x1 y1 x2 y2.
Proof. exact (@lem7034142 x1 y1 x2 y2 R h1 (@lem7034139 R x1 y1 x2 y2 h2)). Qed.
Lemma lem7034146 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term75 R) (h2 : term608 R x1 y1 x2 y2) : term688 R x1 y1 x2 y2.
Proof. exact (fun h0 : term602 R x1 y1 x2 y2 => @lem7034145 R x1 y1 x2 y2 h1 h2). Qed.
Lemma lem7034148 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034149 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term688 R x1 y1 x2 y2) = (term519 R x1 y1 x2 y2).
Proof. exact (@lem7034148 (term519 R x1 y1 x2 y2)). Qed.
Lemma lem7034150 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term75 R) (h2 : term608 R x1 y1 x2 y2) : term519 R x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem7034149 R x1 y1 x2 y2) (@lem7034146 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7034153 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7034155 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term602 R x1 y1 x2 y2) = (term689 R x1 y1 x2 y2).
Proof. exact (@lem7034153 (term519 R x1 y1 x2 y2)). Qed.
Lemma lem7034158 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term608 R x1 y1 x2 y2) : term689 R x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem7034155 R x1 y1 x2 y2) (@lem7033980 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7034161 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term75 R) (h2 : term608 R x1 y1 x2 y2) : False.
Proof. exact (@lem7034158 R x1 y1 x2 y2 h2 (@lem7034150 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7034162 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term75 R) (h2 : term608 R x1 y1 x2 y2) : term690.
Proof. exact (fun h0 : ~ False => @lem7034161 R x1 y1 x2 y2 h1 h2). Qed.
Lemma lem7034164 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034165 : term690 = False.
Proof. exact (@lem7034164 False). Qed.
Lemma lem7034166 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term75 R) (h2 : term608 R x1 y1 x2 y2) : False.
Proof. exact (EQ_MP (@lem7034165) (@lem7034162 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7034168 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7033246 A s) (@lem7033026 A s h1)). Qed.
Lemma lem7034169 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term691 A s.
Proof. exact (fun h0 : term584 A s => @lem7034168 A s h1). Qed.
Lemma lem7034171 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034172 {A : Type'} (s : A -> Prop) : (term691 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7034171 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7034173 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7034172 A s) (@lem7034169 A s h1)). Qed.
Lemma lem7034175 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7033246 A s) (@lem7033026 A s h1)). Qed.
Lemma lem7034176 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term691 A s.
Proof. exact (fun h0 : term584 A s => @lem7034175 A s h1). Qed.
Lemma lem7034178 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034179 {A : Type'} (s : A -> Prop) : (term691 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7034178 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7034180 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7034179 A s) (@lem7034176 A s h1)). Qed.
Lemma lem7034183 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term554 A R f s g) : term554 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7034184 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term554 A R f s g) : term692 A R f s g.
Proof. exact (fun h0 : term553 A R f s g => @lem7034183 A R f s g h1). Qed.
Lemma lem7034186 (p : Prop) : (term693 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7034187 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term692 A R f s g) = (term554 A R f s g).
Proof. exact (@lem7034186 (term553 A R f s g)). Qed.
Lemma lem7034188 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term554 A R f s g) : term554 A R f s g.
Proof. exact (EQ_MP (@lem7034187 A R f s g) (@lem7034184 A R f s g h1)). Qed.
Lemma lem7034194 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7034195 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term667 A x R _93899 _93901 _93900) = (term694 A x R _93899 _93901 _93900).
Proof. exact (@lem7034194 (term579 A x _93899 _93900 _93901) (term584 A _93901) (term553 A R _93899 _93901 _93900)). Qed.
Lemma lem7034209 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7034210 {A : Type'} (R : type1605) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term695 A R _93899 _93901 _93900) = (term696 A R _93899 _93900 _93901).
Proof. exact (@lem7034209 (term553 A R _93899 _93901 _93900) (term584 A _93901)). Qed.
Lemma lem7034216 {A : Type'} (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term697 A x _93899 _93900 _93901) = (term697 A x _93899 _93900 _93901).
Proof. exact (eq_refl (term697 A x _93899 _93900 _93901)). Qed.
Lemma lem7034217 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term694 A x R _93899 _93901 _93900) = (term698 A x R _93899 _93900 _93901).
Proof. exact (MK_COMB (@lem7034216 A x _93899 _93900 _93901) (@lem7034210 A R _93899 _93900 _93901)). Qed.
Lemma lem7034228 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term667 A x R _93899 _93901 _93900) = (term698 A x R _93899 _93900 _93901).
Proof. exact (TRANS (@lem7034195 A x R _93899 _93901 _93900) (@lem7034217 A x R _93899 _93900 _93901)). Qed.
Lemma lem7034229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7034230 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term699 A x R _93899 _93901 _93900) = (term700 A x R _93899 _93900 _93901).
Proof. exact (MK_COMB (@lem7034229) (@lem7034228 A x R _93899 _93900 _93901)). Qed.
Lemma lem7034244 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7034245 {A : Type'} (R : type1605) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term695 A R _93899 _93901 _93900) = (term696 A R _93899 _93900 _93901).
Proof. exact (@lem7034244 (term553 A R _93899 _93901 _93900) (term584 A _93901)). Qed.
Lemma lem7034251 {A : Type'} (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term697 A x _93899 _93900 _93901) = (term697 A x _93899 _93900 _93901).
Proof. exact (eq_refl (term697 A x _93899 _93900 _93901)). Qed.
Lemma lem7034252 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term694 A x R _93899 _93901 _93900) = (term698 A x R _93899 _93900 _93901).
Proof. exact (MK_COMB (@lem7034251 A x _93899 _93900 _93901) (@lem7034245 A R _93899 _93900 _93901)). Qed.
Lemma lem7034263 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : ((term667 A x R _93899 _93901 _93900) = (term694 A x R _93899 _93901 _93900)) = ((term698 A x R _93899 _93900 _93901) = (term698 A x R _93899 _93900 _93901)).
Proof. exact (MK_COMB (@lem7034230 A x R _93899 _93900 _93901) (@lem7034252 A x R _93899 _93900 _93901)). Qed.
Lemma lem7034265 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7034266 (x : Prop) : (x = x) = True.
Proof. exact (@lem7034265 Prop x). Qed.
Lemma lem7034267 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : ((term698 A x R _93899 _93900 _93901) = (term698 A x R _93899 _93900 _93901)) = True.
Proof. exact (@lem7034266 (term698 A x R _93899 _93900 _93901)). Qed.
Lemma lem7034268 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : ((term667 A x R _93899 _93901 _93900) = (term694 A x R _93899 _93901 _93900)) = True.
Proof. exact (TRANS (@lem7034263 A x R _93899 _93900 _93901) (@lem7034267 A x R _93899 _93900 _93901)). Qed.
Lemma lem7034269 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : True = ((term667 A x R _93899 _93901 _93900) = (term694 A x R _93899 _93901 _93900)).
Proof. exact (SYM (@lem7034268 A x R _93899 _93901 _93900)). Qed.
Lemma lem7034270 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term667 A x R _93899 _93901 _93900) = (term694 A x R _93899 _93901 _93900).
Proof. exact (EQ_MP (@lem7034269 A x R _93899 _93901 _93900) (@lem0)). Qed.
Lemma lem7034271 {A : Type'} (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term694 A x R _93899 _93901 _93900.
Proof. exact (EQ_MP (@lem7034270 A x R _93899 _93901 _93900) (@lem7034018 A _93899 _93901 _93900 x R h1)). Qed.
Lemma lem7034273 (b : Prop) (a : Prop) : (a \/ b) = (term676 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7034274 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term694 A x R _93899 _93901 _93900) = (term701 A R x _93899 _93900 _93901).
Proof. exact (@lem7034273 (term695 A R _93899 _93901 _93900) (term579 A x _93899 _93900 _93901)). Qed.
Lemma lem7034276 (a : Prop) (b : Prop) : (term679 a b) = (term680 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7034277 {A : Type'} (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term702 A R _93899 _93901 _93900) = (term703 A R _93899 _93901 _93900).
Proof. exact (@lem7034276 (term584 A _93901) (term553 A R _93899 _93901 _93900)). Qed.
Lemma lem7034279 (a : Prop) : (term218 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7034280 {A : Type'} (_93901 : A -> Prop) : (term704 A _93901) = (@I ((A -> Prop) -> Prop) (@FINITE A) _93901).
Proof. exact (@lem7034279 (@I ((A -> Prop) -> Prop) (@FINITE A) _93901)). Qed.
Lemma lem7034281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7034282 {A : Type'} (_93901 : A -> Prop) : (term705 A _93901) = (term706 A _93901).
Proof. exact (MK_COMB (@lem7034281) (@lem7034280 A _93901)). Qed.
Lemma lem7034283 {A : Type'} (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term554 A R _93899 _93901 _93900) = (term554 A R _93899 _93901 _93900).
Proof. exact (eq_refl (term554 A R _93899 _93901 _93900)). Qed.
Lemma lem7034284 {A : Type'} (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term703 A R _93899 _93901 _93900) = (term707 A R _93899 _93901 _93900).
Proof. exact (MK_COMB (@lem7034282 A _93901) (@lem7034283 A R _93899 _93901 _93900)). Qed.
Lemma lem7034285 {A : Type'} (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term702 A R _93899 _93901 _93900) = (term707 A R _93899 _93901 _93900).
Proof. exact (TRANS (@lem7034277 A R _93899 _93901 _93900) (@lem7034284 A R _93899 _93901 _93900)). Qed.
Lemma lem7034286 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7034287 {A : Type'} (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term708 A R _93899 _93901 _93900) = (term709 A R _93899 _93901 _93900).
Proof. exact (MK_COMB (@lem7034286) (@lem7034285 A R _93899 _93901 _93900)). Qed.
Lemma lem7034288 {A : Type'} (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term579 A x _93899 _93900 _93901) = (term579 A x _93899 _93900 _93901).
Proof. exact (eq_refl (term579 A x _93899 _93900 _93901)). Qed.
Lemma lem7034289 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term701 A R x _93899 _93900 _93901) = (term710 A R x _93899 _93900 _93901).
Proof. exact (MK_COMB (@lem7034287 A R _93899 _93901 _93900) (@lem7034288 A x _93899 _93900 _93901)). Qed.
Lemma lem7034290 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term694 A x R _93899 _93901 _93900) = (term710 A R x _93899 _93900 _93901).
Proof. exact (TRANS (@lem7034274 A R x _93899 _93900 _93901) (@lem7034289 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034292 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : @FINITE A s) (h2 : term554 A R f s g) : term707 A R f s g.
Proof. exact (conj (@lem7034180 A s h1) (@lem7034188 A R f s g h2)). Qed.
Lemma lem7034294 {A : Type'} (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term710 A R x _93899 _93900 _93901.
Proof. exact (EQ_MP (@lem7034290 A R x _93899 _93900 _93901) (@lem7034271 A _93899 _93901 _93900 x R h1)). Qed.
Lemma lem7034295 {A : Type'} (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term710 A R x _93899 _93900 _93901.
Proof. exact (@lem7034294 A _93899 _93900 _93901 x R h1). Qed.
Lemma lem7034296 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term710 A R x f g s.
Proof. exact (@lem7034295 A f g s x R h1). Qed.
Lemma lem7034299 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term600 A x R) (h2 : @FINITE A s) (h3 : term554 A R f s g) : term579 A x f g s.
Proof. exact (@lem7034296 A f g s x R h1 (@lem7034292 A R f s g h2 h3)). Qed.
Lemma lem7034300 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term600 A x R) (h2 : @FINITE A s) (h3 : term554 A R f s g) : term711 A x f g s.
Proof. exact (fun h0 : term712 A x f g s => @lem7034299 A x R f s g h1 h2 h3). Qed.
Lemma lem7034302 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034303 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term711 A x f g s) = (term579 A x f g s).
Proof. exact (@lem7034302 (term579 A x f g s)). Qed.
Lemma lem7034304 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term600 A x R) (h2 : @FINITE A s) (h3 : term554 A R f s g) : term579 A x f g s.
Proof. exact (EQ_MP (@lem7034303 A x f g s) (@lem7034300 A x R f s g h1 h2 h3)). Qed.
Lemma lem7034310 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7034311 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) (s : A -> Prop) : (term545 A s R f g _93898) = (term713 A R f g _93898 s).
Proof. exact (@lem7034310 (term539 A R f g _93898) (term542 A _93898 s)). Qed.
Lemma lem7034317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7034318 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) (s : A -> Prop) : (term714 A s R f g _93898) = (term715 A R f g _93898 s).
Proof. exact (MK_COMB (@lem7034317) (@lem7034311 A R f g _93898 s)). Qed.
Lemma lem7034324 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) (s : A -> Prop) : (term713 A R f g _93898 s) = (term713 A R f g _93898 s).
Proof. exact (eq_refl (term713 A R f g _93898 s)). Qed.
Lemma lem7034325 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) (s : A -> Prop) : ((term545 A s R f g _93898) = (term713 A R f g _93898 s)) = ((term713 A R f g _93898 s) = (term713 A R f g _93898 s)).
Proof. exact (MK_COMB (@lem7034318 A R f g _93898 s) (@lem7034324 A R f g _93898 s)). Qed.
Lemma lem7034327 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7034328 (x : Prop) : (x = x) = True.
Proof. exact (@lem7034327 Prop x). Qed.
Lemma lem7034329 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) (s : A -> Prop) : ((term713 A R f g _93898 s) = (term713 A R f g _93898 s)) = True.
Proof. exact (@lem7034328 (term713 A R f g _93898 s)). Qed.
Lemma lem7034330 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) (s : A -> Prop) : ((term545 A s R f g _93898) = (term713 A R f g _93898 s)) = True.
Proof. exact (TRANS (@lem7034325 A R f g _93898 s) (@lem7034329 A R f g _93898 s)). Qed.
Lemma lem7034331 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) (s : A -> Prop) : True = ((term545 A s R f g _93898) = (term713 A R f g _93898 s)).
Proof. exact (SYM (@lem7034330 A R f g _93898 s)). Qed.
Lemma lem7034332 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) (s : A -> Prop) : (term545 A s R f g _93898) = (term713 A R f g _93898 s).
Proof. exact (EQ_MP (@lem7034331 A R f g _93898 s) (@lem0)). Qed.
Lemma lem7034333 {A : Type'} (_93898 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term713 A R f g _93898 s.
Proof. exact (EQ_MP (@lem7034332 A R f g _93898 s) (@lem7034004 A _93898 s R f g h1)). Qed.
Lemma lem7034335 (b : Prop) (a : Prop) : (a \/ b) = (term676 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7034336 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) : (term713 A R f g _93898 s) = (term716 A s R f g _93898).
Proof. exact (@lem7034335 (term542 A _93898 s) (term539 A R f g _93898)). Qed.
Lemma lem7034338 (a : Prop) : (term218 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7034339 {A : Type'} (_93898 : A) (s : A -> Prop) : (term717 A _93898 s) = (term540 A _93898 s).
Proof. exact (@lem7034338 (term540 A _93898 s)). Qed.
Lemma lem7034340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7034341 {A : Type'} (_93898 : A) (s : A -> Prop) : (term718 A _93898 s) = (term719 A _93898 s).
Proof. exact (MK_COMB (@lem7034340) (@lem7034339 A _93898 s)). Qed.
Lemma lem7034342 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) : (term539 A R f g _93898) = (term539 A R f g _93898).
Proof. exact (eq_refl (term539 A R f g _93898)). Qed.
Lemma lem7034343 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) : (term716 A s R f g _93898) = (term720 A s R f g _93898).
Proof. exact (MK_COMB (@lem7034341 A _93898 s) (@lem7034342 A R f g _93898)). Qed.
Lemma lem7034344 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (_93898 : A) : (term713 A R f g _93898 s) = (term720 A s R f g _93898).
Proof. exact (TRANS (@lem7034336 A s R f g _93898) (@lem7034343 A s R f g _93898)). Qed.
Lemma lem7034347 {A : Type'} (_93898 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term720 A s R f g _93898.
Proof. exact (EQ_MP (@lem7034344 A s R f g _93898) (@lem7034333 A _93898 s R f g h1)). Qed.
Lemma lem7034348 {A : Type'} (_93898 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term720 A s R f g _93898.
Proof. exact (@lem7034347 A _93898 s R f g h1). Qed.
Lemma lem7034349 {A : Type'} (x : type695 A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term721 A R x f g s.
Proof. exact (@lem7034348 A (term557 A x f g s) s R f g h1). Qed.
Lemma lem7034352 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) (h4 : term554 A R f s g) : term570 A R x f g s.
Proof. exact (@lem7034349 A x s R f g h1 (@lem7034304 A x R f s g h2 h3 h4)). Qed.
Lemma lem7034353 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) (h4 : term554 A R f s g) : term722 A R x f g s.
Proof. exact (fun h0 : term572 A R x f g s => @lem7034352 A x R f s g h1 h2 h3 h4). Qed.
Lemma lem7034355 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034356 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term722 A R x f g s) = (term570 A R x f g s).
Proof. exact (@lem7034355 (term570 A R x f g s)). Qed.
Lemma lem7034357 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) (h4 : term554 A R f s g) : term570 A R x f g s.
Proof. exact (EQ_MP (@lem7034356 A R x f g s) (@lem7034353 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7034373 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7034374 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term723 A x R _93899 _93901 _93900) = (term724 A R x _93899 _93900 _93901).
Proof. exact (@lem7034373 (term553 A R _93899 _93901 _93900) (term572 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034380 {A : Type'} (_93901 : A -> Prop) : (term585 A _93901) = (term585 A _93901).
Proof. exact (eq_refl (term585 A _93901)). Qed.
Lemma lem7034381 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term668 A x R _93899 _93901 _93900) = (term725 A R x _93899 _93900 _93901).
Proof. exact (MK_COMB (@lem7034380 A _93901) (@lem7034374 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034385 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7034386 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term725 A R x _93899 _93900 _93901) = (term726 A R x _93899 _93900 _93901).
Proof. exact (@lem7034385 (term553 A R _93899 _93901 _93900) (term584 A _93901) (term572 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034402 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term668 A x R _93899 _93901 _93900) = (term726 A R x _93899 _93900 _93901).
Proof. exact (TRANS (@lem7034381 A R x _93899 _93900 _93901) (@lem7034386 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7034404 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term727 A x R _93899 _93901 _93900) = (term728 A R x _93899 _93900 _93901).
Proof. exact (MK_COMB (@lem7034403) (@lem7034402 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034420 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term726 A R x _93899 _93900 _93901) = (term726 A R x _93899 _93900 _93901).
Proof. exact (eq_refl (term726 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034421 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : ((term668 A x R _93899 _93901 _93900) = (term726 A R x _93899 _93900 _93901)) = ((term726 A R x _93899 _93900 _93901) = (term726 A R x _93899 _93900 _93901)).
Proof. exact (MK_COMB (@lem7034404 A R x _93899 _93900 _93901) (@lem7034420 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034423 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7034424 (x : Prop) : (x = x) = True.
Proof. exact (@lem7034423 Prop x). Qed.
Lemma lem7034425 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : ((term726 A R x _93899 _93900 _93901) = (term726 A R x _93899 _93900 _93901)) = True.
Proof. exact (@lem7034424 (term726 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034426 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : ((term668 A x R _93899 _93901 _93900) = (term726 A R x _93899 _93900 _93901)) = True.
Proof. exact (TRANS (@lem7034421 A R x _93899 _93900 _93901) (@lem7034425 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034427 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : True = ((term668 A x R _93899 _93901 _93900) = (term726 A R x _93899 _93900 _93901)).
Proof. exact (SYM (@lem7034426 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034428 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term668 A x R _93899 _93901 _93900) = (term726 A R x _93899 _93900 _93901).
Proof. exact (EQ_MP (@lem7034427 A R x _93899 _93900 _93901) (@lem0)). Qed.
Lemma lem7034429 {A : Type'} (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term726 A R x _93899 _93900 _93901.
Proof. exact (EQ_MP (@lem7034428 A R x _93899 _93900 _93901) (@lem7034030 A _93899 _93901 _93900 x R h1)). Qed.
Lemma lem7034431 (b : Prop) (a : Prop) : (a \/ b) = (term676 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7034432 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term726 A R x _93899 _93900 _93901) = (term729 A x R _93899 _93901 _93900).
Proof. exact (@lem7034431 (term650 A R x _93899 _93900 _93901) (term553 A R _93899 _93901 _93900)). Qed.
Lemma lem7034434 (a : Prop) (b : Prop) : (term679 a b) = (term680 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7034435 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term730 A R x _93899 _93900 _93901) = (term731 A R x _93899 _93900 _93901).
Proof. exact (@lem7034434 (term584 A _93901) (term572 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034437 (a : Prop) : (term218 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7034438 {A : Type'} (_93901 : A -> Prop) : (term704 A _93901) = (@I ((A -> Prop) -> Prop) (@FINITE A) _93901).
Proof. exact (@lem7034437 (@I ((A -> Prop) -> Prop) (@FINITE A) _93901)). Qed.
Lemma lem7034439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7034440 {A : Type'} (_93901 : A -> Prop) : (term705 A _93901) = (term706 A _93901).
Proof. exact (MK_COMB (@lem7034439) (@lem7034438 A _93901)). Qed.
Lemma lem7034442 (a : Prop) : (term218 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7034443 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term732 A R x _93899 _93900 _93901) = (term570 A R x _93899 _93900 _93901).
Proof. exact (@lem7034442 (term570 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034444 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term731 A R x _93899 _93900 _93901) = (term733 A R x _93899 _93900 _93901).
Proof. exact (MK_COMB (@lem7034440 A _93901) (@lem7034443 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034445 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term730 A R x _93899 _93900 _93901) = (term733 A R x _93899 _93900 _93901).
Proof. exact (TRANS (@lem7034435 A R x _93899 _93900 _93901) (@lem7034444 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034446 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7034447 {A : Type'} (R : type1605) (x : type695 A) (_93899 : A -> nat) (_93900 : A -> nat) (_93901 : A -> Prop) : (term734 A R x _93899 _93900 _93901) = (term735 A R x _93899 _93900 _93901).
Proof. exact (MK_COMB (@lem7034446) (@lem7034445 A R x _93899 _93900 _93901)). Qed.
Lemma lem7034448 {A : Type'} (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term553 A R _93899 _93901 _93900) = (term553 A R _93899 _93901 _93900).
Proof. exact (eq_refl (term553 A R _93899 _93901 _93900)). Qed.
Lemma lem7034449 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term729 A x R _93899 _93901 _93900) = (term736 A x R _93899 _93901 _93900).
Proof. exact (MK_COMB (@lem7034447 A R x _93899 _93900 _93901) (@lem7034448 A R _93899 _93901 _93900)). Qed.
Lemma lem7034450 {A : Type'} (x : type695 A) (R : type1605) (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) : (term726 A R x _93899 _93900 _93901) = (term736 A x R _93899 _93901 _93900).
Proof. exact (TRANS (@lem7034432 A x R _93899 _93901 _93900) (@lem7034449 A x R _93899 _93901 _93900)). Qed.
Lemma lem7034452 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) (h4 : term554 A R f s g) : term733 A R x f g s.
Proof. exact (conj (@lem7034173 A s h3) (@lem7034357 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7034454 {A : Type'} (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term736 A x R _93899 _93901 _93900.
Proof. exact (EQ_MP (@lem7034450 A x R _93899 _93901 _93900) (@lem7034429 A _93899 _93900 _93901 x R h1)). Qed.
Lemma lem7034455 {A : Type'} (_93899 : A -> nat) (_93901 : A -> Prop) (_93900 : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term736 A x R _93899 _93901 _93900.
Proof. exact (@lem7034454 A _93899 _93901 _93900 x R h1). Qed.
Lemma lem7034456 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : type695 A) (R : type1605) (h1 : term600 A x R) : term736 A x R f s g.
Proof. exact (@lem7034455 A f s g x R h1). Qed.
Lemma lem7034459 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) (h4 : term554 A R f s g) : term553 A R f s g.
Proof. exact (@lem7034456 A f s g x R h2 (@lem7034452 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7034460 {A : Type'} (f : A -> nat) (g : A -> nat) (x : type695 A) (R : type1605) (s : A -> Prop) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) : term737 A R f s g.
Proof. exact (fun h0 : term554 A R f s g => @lem7034459 A x R f s g h1 h2 h3 h0). Qed.
Lemma lem7034462 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034463 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term737 A R f s g) = (term553 A R f s g).
Proof. exact (@lem7034462 (term553 A R f s g)). Qed.
Lemma lem7034464 {A : Type'} (f : A -> nat) (g : A -> nat) (x : type695 A) (R : type1605) (s : A -> Prop) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) : term553 A R f s g.
Proof. exact (EQ_MP (@lem7034463 A R f s g) (@lem7034460 A f g x R s h1 h2 h3)). Qed.
Lemma lem7034467 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7034469 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term554 A R f s g) = (term738 A R f s g).
Proof. exact (@lem7034467 (term553 A R f s g)). Qed.
Lemma lem7034472 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term238 A R f s g) : term738 A R f s g.
Proof. exact (EQ_MP (@lem7034469 A R f s g) (@lem7034006 A R f s g h1)). Qed.
Lemma lem7034475 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) (h4 : term238 A R f s g) : False.
Proof. exact (@lem7034472 A R f s g h4 (@lem7034464 A f g x R s h1 h2 h3)). Qed.
Lemma lem7034476 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) (h4 : term238 A R f s g) : term690.
Proof. exact (fun h0 : ~ False => @lem7034475 A x R f s g h1 h2 h3 h4). Qed.
Lemma lem7034478 (p : Prop) : (term670 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7034479 : term690 = False.
Proof. exact (@lem7034478 False). Qed.
Lemma lem7034480 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term600 A x R) (h3 : @FINITE A s) (h4 : term238 A R f s g) : False.
Proof. exact (EQ_MP (@lem7034479) (@lem7034476 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7034481 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term238 A R f s g) (h5 : term498 A x1 y1 x2 y2 x R) : False.
Proof. exact (or_elim (@lem7033652 A x1 y1 x2 y2 x R h5) (fun h0 : term608 R x1 y1 x2 y2 => @lem7034166 R x1 y1 x2 y2 h2 h0) (fun h0 : term600 A x R => @lem7034480 A x R f s g h1 h0 h3 h4)). Qed.
Lemma lem7034482 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : term501 A x1 y1 x2 y2 R) (h4 : @FINITE A s) (h5 : term238 A R f s g) : False.
Proof. exact (ex_elim (@lem7033099 A x1 y1 x2 y2 R h3) (fun x : type695 A => fun h0 : term500 A x1 y1 x2 y2 R x => @lem7034481 A f s g x1 y1 x2 y2 x R h1 h2 h4 h5 h0)). Qed.
Lemma lem7034483 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : term503 A x1 y1 x2 R) (h4 : @FINITE A s) (h5 : term238 A R f s g) : False.
Proof. exact (ex_elim (@lem7033098 A x1 y1 x2 R h3) (fun y2 : nat => fun h0 : term502 A x1 y1 x2 R y2 => @lem7034482 A x1 y1 x2 y2 R f s g h1 h2 h0 h4 h5)). Qed.
Lemma lem7034484 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : term505 A x1 y1 R) (h4 : @FINITE A s) (h5 : term238 A R f s g) : False.
Proof. exact (ex_elim (@lem7033097 A x1 y1 R h3) (fun x2 : nat => fun h0 : term504 A x1 y1 R x2 => @lem7034483 A x1 y1 x2 R f s g h1 h2 h0 h4 h5)). Qed.
Lemma lem7034485 {A : Type'} (x1 : nat) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : term507 A x1 R) (h4 : @FINITE A s) (h5 : term238 A R f s g) : False.
Proof. exact (ex_elim (@lem7033096 A x1 R h3) (fun y1 : nat => fun h0 : term506 A x1 R y1 => @lem7034484 A x1 y1 R f s g h1 h2 h0 h4 h5)). Qed.
Lemma lem7034486 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term238 A R f s g) (h5 : term205 A R) : False.
Proof. exact (ex_elim (@lem7033020 A R h5) (fun x1 : nat => fun h0 : term508 A R x1 => @lem7034485 A x1 R f s g h1 h2 h0 h3 h4)). Qed.
Lemma lem7034487 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term238 A R f s g) (h5 : term205 A R) : (term238 A R f s g) = False.
Proof. exact (prop_ext (fun h6 : term238 A R f s g => @lem7034486 A f s g R h1 h2 h3 h4 h5) (fun h6 : False => @lem7033095 A R f s g h4)). Qed.
Lemma lem7034488 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term238 A R f s g) (h5 : term205 A R) : False.
Proof. exact (EQ_MP (@lem7034487 A f s g R h1 h2 h3 h4 h5) (@lem7033095 A R f s g h4)). Qed.
Lemma lem7034489 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term238 A R f s g) (h5 : term205 A R) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A s => @lem7034488 A f s g R h1 h2 h3 h4 h5) (fun h6 : False => @lem7033026 A s h3)). Qed.
Lemma lem7034490 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term238 A R f s g) (h5 : term205 A R) : False.
Proof. exact (EQ_MP (@lem7034489 A f s g R h1 h2 h3 h4 h5) (@lem7033026 A s h3)). Qed.
Lemma lem7034491 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term238 A R f s g) (h5 : term205 A R) : (term238 A R f s g) = False.
Proof. exact (prop_ext (fun h6 : term238 A R f s g => @lem7034490 A f s g R h1 h2 h3 h4 h5) (fun h6 : False => @lem7032324 A R f s g h4)). Qed.
Lemma lem7034492 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term238 A R f s g) (h5 : term205 A R) : False.
Proof. exact (EQ_MP (@lem7034491 A f s g R h1 h2 h3 h4 h5) (@lem7032324 A R f s g h4)). Qed.
Lemma lem7034493 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term205 A R) : term237 A R f s g.
Proof. exact (fun h0 : term238 A R f s g => @lem7034492 A f s g R h1 h2 h3 h0 h4). Qed.
Lemma lem7034494 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (R : type1605) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term205 A R) : term25 A R f s g.
Proof. exact (EQ_MP (@lem7032323 A R f s g) (@lem7034493 A f g s R h1 h2 h3 h4)). Qed.
Lemma lem7034495 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (R : type1605) (h1 : term75 R) (h2 : @FINITE A s) (h3 : term205 A R) : term229 A R f s g.
Proof. exact (fun h0 : term80 A s R f g => @lem7034494 A f g s R h0 h1 h2 h3). Qed.
Lemma lem7034496 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term75 R) (h2 : term205 A R) : term79 A R f s g.
Proof. exact (fun h0 : @FINITE A s => @lem7034495 A f g s R h1 h0 h2). Qed.
Lemma lem7034501 {A : Type'} (f : A -> nat) (g : A -> nat) (R : type1605) (h1 : term75 R) (h2 : term205 A R) : term112 A R f g.
Proof. exact (fun s : A -> Prop => @lem7034496 A f s g R h1 h2). Qed.
Lemma lem7034506 {A : Type'} (f : A -> nat) (R : type1605) (h1 : term75 R) (h2 : term205 A R) : term143 A R f.
Proof. exact (fun g : A -> nat => @lem7034501 A f g R h1 h2). Qed.
Lemma lem7034511 {A : Type'} (R : type1605) (h1 : term75 R) (h2 : term205 A R) : term172 A R.
Proof. exact (fun f : A -> nat => @lem7034506 A f R h1 h2). Qed.
Lemma lem7034512 {A : Type'} (R : type1605) (h1 : term75 R) : term209 A R.
Proof. exact (fun h0 : term205 A R => @lem7034511 A R h1 h0). Qed.
Lemma lem7034513 {A : Type'} (R : type1605) : term220 A R.
Proof. exact (fun h0 : term75 R => @lem7034512 A R h0). Qed.
Lemma lem7034514 {A : Type'} (R : type1605) : term221 A R.
Proof. exact (fun h0 : term23 R => @lem7034513 A R). Qed.
Lemma lem7034519 {A : Type'} : term225 A.
Proof. exact (fun R : type1605 => @lem7034514 A R). Qed.
Lemma lem7034520 {A : Type'} : term224 A.
Proof. exact (EQ_MP (@lem7032314 A) (@lem7034519 A)). Qed.
Lemma lem7034521 {A : Type'} (R : type1605) : term739 A R.
Proof. exact (@lem7034520 A R). Qed.
Lemma lem7034522 {A : Type'} (R : type1605) : (term739 A R) = (term213 A R).
Proof. exact (eq_refl (term739 A R)). Qed.
Lemma lem7034523 {A : Type'} (R : type1605) : term213 A R.
Proof. exact (EQ_MP (@lem7034522 A R) (@lem7034521 A R)). Qed.
Lemma lem7034525 {A : Type'} (R : type1605) : term213 A R.
Proof. exact (@lem7031950 A R (@lem7034523 A R)). Qed.
Lemma lem7034526 {A : Type'} (R : type1605) (h1 : term23 R) : term219 A R.
Proof. exact (@lem7034525 A R (@lem7031756 R h1)). Qed.
Lemma lem7034527 {A : Type'} (R : type1605) (h1 : term75 R) (h2 : term23 R) : term211 A R.
Proof. exact (@lem7034526 A R h2 (@lem7031757 R h1)). Qed.
Lemma lem7034528 {A : Type'} (R : type1605) (h1 : term75 R) (h2 : term212 A R) (h3 : term23 R) : False.
Proof. exact (@lem7034527 A R h1 h3 (@lem7031934 A R h2)). Qed.
Lemma lem7034529 {A : Type'} (R : type1605) (h1 : term75 R) (h2 : term212 A R) (h3 : term23 R) : (term212 A R) = False.
Proof. exact (prop_ext (fun h4 : term212 A R => @lem7034528 A R h1 h2 h3) (fun h4 : False => @lem7031934 A R h2)). Qed.
Lemma lem7034530 {A : Type'} (R : type1605) (h1 : term75 R) (h2 : term212 A R) (h3 : term23 R) : False.
Proof. exact (EQ_MP (@lem7034529 A R h1 h2 h3) (@lem7031934 A R h2)). Qed.
Lemma lem7034531 {A : Type'} (R : type1605) (h1 : term75 R) (h2 : term23 R) : term211 A R.
Proof. exact (fun h0 : term212 A R => @lem7034530 A R h1 h0 h2). Qed.
Lemma lem7034532 {A : Type'} (R : type1605) (h1 : term75 R) (h2 : term23 R) : term209 A R.
Proof. exact (EQ_MP (@lem7031933 A R) (@lem7034531 A R h1 h2)). Qed.
Lemma lem7034533 {A : Type'} (R : type1605) (h1 : term75 R) (h2 : term23 R) : term208 A R.
Proof. exact (EQ_MP (@lem7031929 A R h2) (@lem7034532 A R h1 h2)). Qed.
Lemma lem7034534 {A : Type'} (R : type1605) (h1 : term75 R) (h2 : term23 R) : term172 A R.
Proof. exact (@lem7034533 A R h1 h2 (@lem7030933 A R)). Qed.
Lemma lem7034535 {A : Type'} (R : type1605) (h1 : term23 R) : term173 A R.
Proof. exact (fun h0 : term75 R => @lem7034534 A R h0 h1). Qed.
Lemma lem7034536 {A : Type'} (R : type1605) : term174 A R.
Proof. exact (fun h0 : term23 R => @lem7034535 A R h0). Qed.
Lemma lem7034541 {A : Type'} : term178 A.
Proof. exact (fun R : type1605 => @lem7034536 A R). Qed.
Lemma lem7034542 {A : Type'} : term177 A.
Proof. exact (EQ_MP (@lem7031755 A) (@lem7034541 A)). Qed.
