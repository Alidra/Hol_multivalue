Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_MONO_LT_term_abbrevs.
Require Import ADD1_spec.
Require Import ADD_SYM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD2_spec.
Require Import LE_RDIV_EQ_spec.
Require Import LE_REFL_spec.
Require Import LE_SUC_LT_spec.
Require Import LE_TRANS_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem192845 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem192846 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem192847 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem192846 t1) (@lem192845 t1)). Qed.
Lemma lem192848 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem192847 t1 t2). Qed.
Lemma lem192849 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem192850 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem192849 t1 t2) (@lem192848 t1 t2)). Qed.
Lemma lem192851 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem192850 t1 t2 t3). Qed.
Lemma lem192852 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem192853 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem192852 t1 t2 t3) (@lem192851 t1 t2 t3)). Qed.
Lemma lem192854 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem192853 t1 t2 t3)). Qed.
Lemma lem192866 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem192867 (a : nat) (b : nat) : (term8 a b) = (term9 a b).
Proof. exact (@lem192866 (term8 a b)). Qed.
Lemma lem192868 (a : nat) (b : nat) : (term9 a b) = (term8 a b).
Proof. exact (SYM (@lem192867 a b)). Qed.
Lemma lem192869 (a : nat) (b : nat) (h1 : term10 a b) : term10 a b.
Proof. exact (h1). Qed.
Lemma lem192872 (a : nat) (b : nat) (h1 : term11 a b) : term11 a b.
Proof. exact (h1). Qed.
Lemma lem192873 (a : nat) (b : nat) : term12 a b.
Proof. exact (fun h0 : term11 a b => @lem192872 a b h0). Qed.
Lemma lem192874 (a : nat) (b : nat) (h1 : term12 a b) : term12 a b.
Proof. exact (h1). Qed.
Lemma lem192875 (a : nat) (b : nat) (h1 : term11 a b) : term11 a b.
Proof. exact (h1). Qed.
Lemma lem192876 (a : nat) (b : nat) (h1 : term11 a b) (h2 : term12 a b) : term11 a b.
Proof. exact (@lem192874 a b h2 (@lem192875 a b h1)). Qed.
Lemma lem192877 (a : nat) (b : nat) (h1 : term11 a b) : term13 a b.
Proof. exact (fun h0 : term12 a b => @lem192876 a b h1 h0). Qed.
Lemma lem192878 (a : nat) (b : nat) (h1 : term12 a b) : term12 a b.
Proof. exact (h1). Qed.
Lemma lem192879 (a : nat) (b : nat) (h1 : term11 a b) (h2 : term12 a b) : term11 a b.
Proof. exact (@lem192877 a b h1 (@lem192878 a b h2)). Qed.
Lemma lem192880 (a : nat) (b : nat) (h1 : term12 a b) : term12 a b.
Proof. exact (fun h0 : term11 a b => @lem192879 a b h0 h1). Qed.
Lemma lem192881 (a : nat) (b : nat) : term14 a b.
Proof. exact (fun h0 : term12 a b => @lem192880 a b h0). Qed.
Lemma lem192884 (a : nat) (b : nat) : term12 a b.
Proof. exact (@lem192881 a b (@lem192873 a b)). Qed.
Lemma lem192920 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem192921 : term15 = term16.
Proof. exact (@lem192920 term17). Qed.
Lemma lem192926 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem192927 : term19 = term20.
Proof. exact (MK_COMB (@lem192926) (@lem192921)). Qed.
Lemma lem192930 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem192931 : term22 = term23.
Proof. exact (MK_COMB (@lem192930) (@lem192927)). Qed.
Lemma lem192934 (a : nat) (b : nat) : (term24 a b) = (term24 a b).
Proof. exact (eq_refl (term24 a b)). Qed.
Lemma lem192935 (a : nat) (b : nat) : (term11 a b) = (term25 a b).
Proof. exact (MK_COMB (@lem192934 a b) (@lem192931)). Qed.
Lemma lem192938 (b : nat) : (term26 b) = (term27 b).
Proof. exact (fun_ext (fun a : nat => @lem192935 a b)). Qed.
Lemma lem192939 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192940 (b : nat) : (term28 b) = (term29 b).
Proof. exact (MK_COMB (@lem192939) (@lem192938 b)). Qed.
Lemma lem192945 : term30 = term31.
Proof. exact (fun_ext (fun b : nat => @lem192940 b)). Qed.
Lemma lem192946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192955 : term32 = term33.
Proof. exact (MK_COMB (@lem192946) (@lem192945)). Qed.
Lemma lem192956 (m : nat) : ((S m) = (term34 m)) = ((S m) = (term34 m)).
Proof. exact (eq_refl ((S m) = (term34 m))). Qed.
Lemma lem192957 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem192956 m)). Qed.
Lemma lem192958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192959 : term17 = term17.
Proof. exact (MK_COMB (@lem192958) (@lem192957)). Qed.
Lemma lem192960 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem192961 : term16 = term16.
Proof. exact (MK_COMB (@lem192960) (@lem192959)). Qed.
Lemma lem192966 (m : nat) (n : nat) : ((term36 m n) = (Peano.lt m n)) = ((term36 m n) = (Peano.lt m n)).
Proof. exact (eq_refl ((term36 m n) = (Peano.lt m n))). Qed.
Lemma lem192967 (m : nat) : (term37 m) = (term37 m).
Proof. exact (fun_ext (fun n : nat => @lem192966 m n)). Qed.
Lemma lem192968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192969 (m : nat) : (term38 m) = (term38 m).
Proof. exact (MK_COMB (@lem192968) (@lem192967 m)). Qed.
Lemma lem192970 : term39 = term39.
Proof. exact (fun_ext (fun m : nat => @lem192969 m)). Qed.
Lemma lem192971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192972 : term40 = term40.
Proof. exact (MK_COMB (@lem192971) (@lem192970)). Qed.
Lemma lem192973 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem192974 : term18 = term18.
Proof. exact (MK_COMB (@lem192973) (@lem192972)). Qed.
Lemma lem192975 : term20 = term20.
Proof. exact (MK_COMB (@lem192974) (@lem192961)). Qed.
Lemma lem192976 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem192977 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem192976 n)). Qed.
Lemma lem192978 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192979 : term42 = term42.
Proof. exact (MK_COMB (@lem192978) (@lem192977)). Qed.
Lemma lem192980 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem192981 : term21 = term21.
Proof. exact (MK_COMB (@lem192980) (@lem192979)). Qed.
Lemma lem192982 : term23 = term23.
Proof. exact (MK_COMB (@lem192981) (@lem192975)). Qed.
Lemma lem192983 (a : nat) (b : nat) : (Peano.lt a b) = (Peano.lt a b).
Proof. exact (eq_refl (Peano.lt a b)). Qed.
Lemma lem192988 (a : nat) (k : nat) (b : nat) : (term43 a k b) = (term43 a k b).
Proof. exact (eq_refl (term43 a k b)). Qed.
Lemma lem192989 (a : nat) (b : nat) : (term44 a b) = (term44 a b).
Proof. exact (fun_ext (fun k : nat => @lem192988 a k b)). Qed.
Lemma lem192990 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192991 (a : nat) (b : nat) : (term45 a b) = (term45 a b).
Proof. exact (MK_COMB (@lem192990) (@lem192989 a b)). Qed.
Lemma lem192992 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem192993 (a : nat) (b : nat) : (term46 a b) = (term46 a b).
Proof. exact (MK_COMB (@lem192992) (@lem192991 a b)). Qed.
Lemma lem192994 (a : nat) (b : nat) : (term8 a b) = (term8 a b).
Proof. exact (MK_COMB (@lem192993 a b) (@lem192983 a b)). Qed.
Lemma lem192995 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem192996 (a : nat) (b : nat) : (term10 a b) = (term10 a b).
Proof. exact (MK_COMB (@lem192995) (@lem192994 a b)). Qed.
Lemma lem192997 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem192998 (a : nat) (b : nat) : (term24 a b) = (term24 a b).
Proof. exact (MK_COMB (@lem192997) (@lem192996 a b)). Qed.
Lemma lem192999 (a : nat) (b : nat) : (term25 a b) = (term25 a b).
Proof. exact (MK_COMB (@lem192998 a b) (@lem192982)). Qed.
Lemma lem193000 (b : nat) : (term27 b) = (term27 b).
Proof. exact (fun_ext (fun a : nat => @lem192999 a b)). Qed.
Lemma lem193001 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193002 (b : nat) : (term29 b) = (term29 b).
Proof. exact (MK_COMB (@lem193001) (@lem193000 b)). Qed.
Lemma lem193003 : term31 = term31.
Proof. exact (fun_ext (fun b : nat => @lem193002 b)). Qed.
Lemma lem193004 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193005 : term33 = term33.
Proof. exact (MK_COMB (@lem193004) (@lem193003)). Qed.
Lemma lem193060 : term32 = term33.
Proof. exact (TRANS (@lem192955) (@lem193005)). Qed.
Lemma lem193061 : term33 = term32.
Proof. exact (SYM (@lem193060)). Qed.
Lemma lem193062 (a : nat) (b : nat) (h1 : term10 a b) : term10 a b.
Proof. exact (h1). Qed.
Lemma lem193063 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem193064 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem193065 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem193072 (a : nat) (k : nat) (b : nat) : (term43 a k b) = (term47 a k b).
Proof. exact (@lem17265 (Peano.le k a) (term48 k b)). Qed.
Lemma lem193073 (a : nat) (b : nat) : (term44 a b) = (term49 a b).
Proof. exact (fun_ext (fun k : nat => @lem193072 a k b)). Qed.
Lemma lem193074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193075 (a : nat) (b : nat) : (term45 a b) = (term50 a b).
Proof. exact (MK_COMB (@lem193074) (@lem193073 a b)). Qed.
Lemma lem193076 (a : nat) (b : nat) : (term51 a b) = (term51 a b).
Proof. exact (eq_refl (term51 a b)). Qed.
Lemma lem193077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem193078 (a : nat) (b : nat) : (term52 a b) = (term53 a b).
Proof. exact (MK_COMB (@lem193077) (@lem193075 a b)). Qed.
Lemma lem193079 (a : nat) (b : nat) : (term54 a b) = (term55 a b).
Proof. exact (MK_COMB (@lem193078 a b) (@lem193076 a b)). Qed.
Lemma lem193080 (a : nat) (b : nat) : (term10 a b) = (term54 a b).
Proof. exact (@lem17362 (term45 a b) (Peano.lt a b)). Qed.
Lemma lem193133 (a : nat) (b : nat) : (term10 a b) = (term55 a b).
Proof. exact (TRANS (@lem193080 a b) (@lem193079 a b)). Qed.
Lemma lem193134 (a : nat) (b : nat) (h1 : term10 a b) : term55 a b.
Proof. exact (EQ_MP (@lem193133 a b) (@lem193062 a b h1)). Qed.
Lemma lem193135 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem193136 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem193135 n)). Qed.
Lemma lem193137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193146 : term42 = term42.
Proof. exact (MK_COMB (@lem193137) (@lem193136)). Qed.
Lemma lem193147 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem193146) (@lem193063 h1)). Qed.
Lemma lem193162 (m : nat) (n : nat) : ((term36 m n) = (Peano.lt m n)) = (term56 m n).
Proof. exact (@lem17784 (term36 m n) (Peano.lt m n)). Qed.
Lemma lem193163 (m : nat) : (term37 m) = (term57 m).
Proof. exact (fun_ext (fun n : nat => @lem193162 m n)). Qed.
Lemma lem193164 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193165 (m : nat) : (term38 m) = (term58 m).
Proof. exact (MK_COMB (@lem193164) (@lem193163 m)). Qed.
Lemma lem193166 : term39 = term59.
Proof. exact (fun_ext (fun m : nat => @lem193165 m)). Qed.
Lemma lem193167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193168 : term40 = term60.
Proof. exact (MK_COMB (@lem193167) (@lem193166)). Qed.
Lemma lem193174 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term61 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem193175 (P : nat -> Prop) (Q : nat -> Prop) : (term63 P Q) = (term64 P Q).
Proof. exact (@lem193174 nat P Q). Qed.
Lemma lem193176 (m : nat) : (term65 m) = (term66 m).
Proof. exact (@lem193175 (term67 m) (term68 m)). Qed.
Lemma lem193177 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem193178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem193179 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (MK_COMB (@lem193178) (@lem193177 m n)). Qed.
Lemma lem193180 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem193181 (m : nat) (n : nat) : (term75 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem193179 m n) (@lem193180 m n)). Qed.
Lemma lem193182 (m : nat) : (term76 m) = (term57 m).
Proof. exact (fun_ext (fun n : nat => @lem193181 m n)). Qed.
Lemma lem193183 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193184 (m : nat) : (term65 m) = (term58 m).
Proof. exact (MK_COMB (@lem193183) (@lem193182 m)). Qed.
Lemma lem193185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem193186 (m : nat) : (term77 m) = (term78 m).
Proof. exact (MK_COMB (@lem193185) (@lem193184 m)). Qed.
Lemma lem193187 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem193188 (m : nat) : (term79 m) = (term67 m).
Proof. exact (fun_ext (fun n : nat => @lem193187 m n)). Qed.
Lemma lem193189 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193190 (m : nat) : (term80 m) = (term81 m).
Proof. exact (MK_COMB (@lem193189) (@lem193188 m)). Qed.
Lemma lem193191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem193192 (m : nat) : (term82 m) = (term83 m).
Proof. exact (MK_COMB (@lem193191) (@lem193190 m)). Qed.
Lemma lem193193 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem193194 (m : nat) : (term84 m) = (term68 m).
Proof. exact (fun_ext (fun n : nat => @lem193193 m n)). Qed.
Lemma lem193195 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193196 (m : nat) : (term85 m) = (term86 m).
Proof. exact (MK_COMB (@lem193195) (@lem193194 m)). Qed.
Lemma lem193197 (m : nat) : (term66 m) = (term87 m).
Proof. exact (MK_COMB (@lem193192 m) (@lem193196 m)). Qed.
Lemma lem193198 (m : nat) : ((term65 m) = (term66 m)) = ((term58 m) = (term87 m)).
Proof. exact (MK_COMB (@lem193186 m) (@lem193197 m)). Qed.
Lemma lem193199 (m : nat) : (term58 m) = (term87 m).
Proof. exact (EQ_MP (@lem193198 m) (@lem193176 m)). Qed.
Lemma lem193296 : term59 = term88.
Proof. exact (fun_ext (fun m : nat => @lem193199 m)). Qed.
Lemma lem193297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193298 : term60 = term89.
Proof. exact (MK_COMB (@lem193297) (@lem193296)). Qed.
Lemma lem193300 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term61 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem193301 (P : nat -> Prop) (Q : nat -> Prop) : (term63 P Q) = (term64 P Q).
Proof. exact (@lem193300 nat P Q). Qed.
Lemma lem193302 : term90 = term91.
Proof. exact (@lem193301 term92 term93). Qed.
Lemma lem193303 (m : nat) : (term94 m) = (term81 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem193304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem193305 (m : nat) : (term95 m) = (term83 m).
Proof. exact (MK_COMB (@lem193304) (@lem193303 m)). Qed.
Lemma lem193306 (m : nat) : (term96 m) = (term86 m).
Proof. exact (eq_refl (term96 m)). Qed.
Lemma lem193307 (m : nat) : (term97 m) = (term87 m).
Proof. exact (MK_COMB (@lem193305 m) (@lem193306 m)). Qed.
Lemma lem193308 : term98 = term88.
Proof. exact (fun_ext (fun m : nat => @lem193307 m)). Qed.
Lemma lem193309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193310 : term90 = term89.
Proof. exact (MK_COMB (@lem193309) (@lem193308)). Qed.
Lemma lem193311 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem193312 : term99 = term100.
Proof. exact (MK_COMB (@lem193311) (@lem193310)). Qed.
Lemma lem193313 (m : nat) : (term94 m) = (term81 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem193314 : term101 = term92.
Proof. exact (fun_ext (fun m : nat => @lem193313 m)). Qed.
Lemma lem193315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193316 : term102 = term103.
Proof. exact (MK_COMB (@lem193315) (@lem193314)). Qed.
Lemma lem193317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem193318 : term104 = term105.
Proof. exact (MK_COMB (@lem193317) (@lem193316)). Qed.
Lemma lem193319 (m : nat) : (term96 m) = (term86 m).
Proof. exact (eq_refl (term96 m)). Qed.
Lemma lem193320 : term106 = term93.
Proof. exact (fun_ext (fun m : nat => @lem193319 m)). Qed.
Lemma lem193321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193322 : term107 = term108.
Proof. exact (MK_COMB (@lem193321) (@lem193320)). Qed.
Lemma lem193323 : term91 = term109.
Proof. exact (MK_COMB (@lem193318) (@lem193322)). Qed.
Lemma lem193324 : (term90 = term91) = (term89 = term109).
Proof. exact (MK_COMB (@lem193312) (@lem193323)). Qed.
Lemma lem193325 : term89 = term109.
Proof. exact (EQ_MP (@lem193324) (@lem193302)). Qed.
Lemma lem193432 : term60 = term109.
Proof. exact (TRANS (@lem193298) (@lem193325)). Qed.
Lemma lem193433 : term40 = term109.
Proof. exact (TRANS (@lem193168) (@lem193432)). Qed.
Lemma lem193434 (h1 : term40) : term109.
Proof. exact (EQ_MP (@lem193433) (@lem193064 h1)). Qed.
Lemma lem193435 (m : nat) : ((S m) = (term34 m)) = ((S m) = (term34 m)).
Proof. exact (eq_refl ((S m) = (term34 m))). Qed.
Lemma lem193436 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem193435 m)). Qed.
Lemma lem193437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193446 : term17 = term17.
Proof. exact (MK_COMB (@lem193437) (@lem193436)). Qed.
Lemma lem193447 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem193446) (@lem193065 h1)). Qed.
Lemma lem193454 (a : nat) (b : nat) : (term51 a b) = (term51 a b).
Proof. exact (eq_refl (term51 a b)). Qed.
Lemma lem193477 (a : nat) (k : nat) (b : nat) : (term47 a k b) = (term47 a k b).
Proof. exact (eq_refl (term47 a k b)). Qed.
Lemma lem193478 (a : nat) (b : nat) : (term49 a b) = (term49 a b).
Proof. exact (fun_ext (fun k : nat => @lem193477 a k b)). Qed.
Lemma lem193479 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193480 (a : nat) (b : nat) : (term50 a b) = (term50 a b).
Proof. exact (MK_COMB (@lem193479) (@lem193478 a b)). Qed.
Lemma lem193481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem193482 (a : nat) (b : nat) : (term53 a b) = (term53 a b).
Proof. exact (MK_COMB (@lem193481) (@lem193480 a b)). Qed.
Lemma lem193483 (a : nat) (b : nat) : (term55 a b) = (term55 a b).
Proof. exact (MK_COMB (@lem193482 a b) (@lem193454 a b)). Qed.
Lemma lem193484 (a : nat) (b : nat) (h1 : term10 a b) : term55 a b.
Proof. exact (EQ_MP (@lem193483 a b) (@lem193134 a b h1)). Qed.
Lemma lem193489 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem193490 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem193489 n)). Qed.
Lemma lem193491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193492 : term42 = term42.
Proof. exact (MK_COMB (@lem193491) (@lem193490)). Qed.
Lemma lem193493 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem193492) (@lem193147 h1)). Qed.
Lemma lem193510 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem193511 (m : nat) : (term68 m) = (term68 m).
Proof. exact (fun_ext (fun n : nat => @lem193510 m n)). Qed.
Lemma lem193512 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193513 (m : nat) : (term86 m) = (term86 m).
Proof. exact (MK_COMB (@lem193512) (@lem193511 m)). Qed.
Lemma lem193514 : term93 = term93.
Proof. exact (fun_ext (fun m : nat => @lem193513 m)). Qed.
Lemma lem193515 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193516 : term108 = term108.
Proof. exact (MK_COMB (@lem193515) (@lem193514)). Qed.
Lemma lem193533 (m : nat) (n : nat) : (term70 m n) = (term70 m n).
Proof. exact (eq_refl (term70 m n)). Qed.
Lemma lem193534 (m : nat) : (term67 m) = (term67 m).
Proof. exact (fun_ext (fun n : nat => @lem193533 m n)). Qed.
Lemma lem193535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193536 (m : nat) : (term81 m) = (term81 m).
Proof. exact (MK_COMB (@lem193535) (@lem193534 m)). Qed.
Lemma lem193537 : term92 = term92.
Proof. exact (fun_ext (fun m : nat => @lem193536 m)). Qed.
Lemma lem193538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193539 : term103 = term103.
Proof. exact (MK_COMB (@lem193538) (@lem193537)). Qed.
Lemma lem193540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem193541 : term105 = term105.
Proof. exact (MK_COMB (@lem193540) (@lem193539)). Qed.
Lemma lem193542 : term109 = term109.
Proof. exact (MK_COMB (@lem193541) (@lem193516)). Qed.
Lemma lem193543 (h1 : term40) : term109.
Proof. exact (EQ_MP (@lem193542) (@lem193434 h1)). Qed.
Lemma lem193558 (m : nat) : ((S m) = (term34 m)) = ((S m) = (term34 m)).
Proof. exact (eq_refl ((S m) = (term34 m))). Qed.
Lemma lem193559 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem193558 m)). Qed.
Lemma lem193560 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193561 : term17 = term17.
Proof. exact (MK_COMB (@lem193560) (@lem193559)). Qed.
Lemma lem193562 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem193561) (@lem193447 h1)). Qed.
Lemma lem193563 (h1 : term40) : term108.
Proof. exact (proj2 (@lem193543 h1)). Qed.
Lemma lem193566 (a : nat) (b : nat) (h1 : term10 a b) : term50 a b.
Proof. exact (proj1 (@lem193484 a b h1)). Qed.
Lemma lem193568 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem193569 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem193568 n)). Qed.
Lemma lem193570 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193572 : term42 = term42.
Proof. exact (MK_COMB (@lem193570) (@lem193569)). Qed.
Lemma lem193573 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem193572) (@lem193493 h1)). Qed.
Lemma lem193575 (m : nat) : ((S m) = (term34 m)) = ((S m) = (term34 m)).
Proof. exact (eq_refl ((S m) = (term34 m))). Qed.
Lemma lem193576 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem193575 m)). Qed.
Lemma lem193577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193579 : term17 = term17.
Proof. exact (MK_COMB (@lem193577) (@lem193576)). Qed.
Lemma lem193580 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem193579) (@lem193562 h1)). Qed.
Lemma lem193604 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem193605 (m : nat) : (term68 m) = (term68 m).
Proof. exact (fun_ext (fun n : nat => @lem193604 m n)). Qed.
Lemma lem193606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193607 (m : nat) : (term86 m) = (term86 m).
Proof. exact (MK_COMB (@lem193606) (@lem193605 m)). Qed.
Lemma lem193608 : term93 = term93.
Proof. exact (fun_ext (fun m : nat => @lem193607 m)). Qed.
Lemma lem193609 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193611 : term108 = term108.
Proof. exact (MK_COMB (@lem193609) (@lem193608)). Qed.
Lemma lem193612 (h1 : term40) : term108.
Proof. exact (EQ_MP (@lem193611) (@lem193563 h1)). Qed.
Lemma lem193620 (a : nat) (k : nat) (b : nat) : (term47 a k b) = (term47 a k b).
Proof. exact (eq_refl (term47 a k b)). Qed.
Lemma lem193621 (a : nat) (b : nat) : (term49 a b) = (term49 a b).
Proof. exact (fun_ext (fun k : nat => @lem193620 a k b)). Qed.
Lemma lem193622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem193624 (a : nat) (b : nat) : (term50 a b) = (term50 a b).
Proof. exact (MK_COMB (@lem193622) (@lem193621 a b)). Qed.
Lemma lem193625 (a : nat) (b : nat) (h1 : term10 a b) : term50 a b.
Proof. exact (EQ_MP (@lem193624 a b) (@lem193566 a b h1)). Qed.
Lemma lem193630 (_3899 : nat) (h1 : term42) : term110 _3899.
Proof. exact (@lem193573 h1 _3899). Qed.
Lemma lem193631 (_3899 : nat) : (term110 _3899) = (Peano.le _3899 _3899).
Proof. exact (eq_refl (term110 _3899)). Qed.
Lemma lem193633 (_3900 : nat) (h1 : term17) : term111 _3900.
Proof. exact (@lem193580 h1 _3900). Qed.
Lemma lem193634 (_3900 : nat) : (term111 _3900) = ((S _3900) = (term34 _3900)).
Proof. exact (eq_refl (term111 _3900)). Qed.
Lemma lem193642 (_3903 : nat) (h1 : term40) : term96 _3903.
Proof. exact (@lem193612 h1 _3903). Qed.
Lemma lem193643 (_3903 : nat) : (term96 _3903) = (term86 _3903).
Proof. exact (eq_refl (term96 _3903)). Qed.
Lemma lem193644 (_3903 : nat) (h1 : term40) : term86 _3903.
Proof. exact (EQ_MP (@lem193643 _3903) (@lem193642 _3903 h1)). Qed.
Lemma lem193645 (_3903 : nat) (_3904 : nat) (h1 : term40) : term73 _3903 _3904.
Proof. exact (@lem193644 _3903 h1 _3904). Qed.
Lemma lem193646 (_3903 : nat) (_3904 : nat) : (term73 _3903 _3904) = (term74 _3903 _3904).
Proof. exact (eq_refl (term73 _3903 _3904)). Qed.
Lemma lem193648 (_3905 : nat) (a : nat) (b : nat) (h1 : term10 a b) : term112 a b _3905.
Proof. exact (@lem193625 a b h1 _3905). Qed.
Lemma lem193649 (a : nat) (_3905 : nat) (b : nat) : (term112 a b _3905) = (term47 a _3905 b).
Proof. exact (eq_refl (term112 a b _3905)). Qed.
Lemma lem193666 (_3903 : nat) (_3904 : nat) (h1 : term40) : term74 _3903 _3904.
Proof. exact (EQ_MP (@lem193646 _3903 _3904) (@lem193645 _3903 _3904 h1)). Qed.
Lemma lem193672 (_3905 : nat) (a : nat) (b : nat) (h1 : term10 a b) : term47 a _3905 b.
Proof. exact (EQ_MP (@lem193649 a _3905 b) (@lem193648 _3905 a b h1)). Qed.
Lemma lem193674 (a : nat) (b : nat) (h1 : term10 a b) : term51 a b.
Proof. exact (proj2 (@lem193484 a b h1)). Qed.
Lemma lem193694 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem193695 (_3910 : nat) (_3912 : nat) (h1 : _3910 = _3912) : _3910 = _3912.
Proof. exact (h1). Qed.
Lemma lem193696 (_3911 : nat) (_3913 : nat) (h1 : _3911 = _3913) : _3911 = _3913.
Proof. exact (h1). Qed.
Lemma lem193697 (_3910 : nat) (_3912 : nat) (h1 : _3910 = _3912) : (Peano.le _3910) = (Peano.le _3912).
Proof. exact (MK_COMB (@lem193694) (@lem193695 _3910 _3912 h1)). Qed.
Lemma lem193698 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) (h1 : _3910 = _3912) (h2 : _3911 = _3913) : (Peano.le _3910 _3911) = (Peano.le _3912 _3913).
Proof. exact (MK_COMB (@lem193697 _3910 _3912 h1) (@lem193696 _3911 _3913 h2)). Qed.
Lemma lem193700 (b : Prop) (a : Prop) : term113 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem193701 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : term114 _3912 _3913 _3910 _3911.
Proof. exact (@lem193700 (Peano.le _3912 _3913) (Peano.le _3910 _3911)). Qed.
Lemma lem193702 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) (h1 : _3910 = _3912) (h2 : _3911 = _3913) : term115 _3912 _3913 _3910 _3911.
Proof. exact (@lem193701 _3912 _3913 _3910 _3911 (@lem193698 _3910 _3912 _3911 _3913 h1 h2)). Qed.
Lemma lem193703 (_3913 : nat) (_3911 : nat) (_3910 : nat) (_3912 : nat) (h1 : _3910 = _3912) : term116 _3912 _3913 _3910 _3911.
Proof. exact (fun h0 : _3911 = _3913 => @lem193702 _3910 _3912 _3911 _3913 h1 h0). Qed.
Lemma lem193705 (a : Prop) (b : Prop) : (a -> b) = (term117 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem193706 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term116 _3912 _3913 _3910 _3911) = (term118 _3912 _3913 _3910 _3911).
Proof. exact (@lem193705 (_3911 = _3913) (term115 _3912 _3913 _3910 _3911)). Qed.
Lemma lem193707 (_3913 : nat) (_3911 : nat) (_3910 : nat) (_3912 : nat) (h1 : _3910 = _3912) : term118 _3912 _3913 _3910 _3911.
Proof. exact (EQ_MP (@lem193706 _3912 _3913 _3910 _3911) (@lem193703 _3913 _3911 _3910 _3912 h1)). Qed.
Lemma lem193708 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : term119 _3912 _3913 _3910 _3911.
Proof. exact (fun h0 : _3910 = _3912 => @lem193707 _3913 _3911 _3910 _3912 h0). Qed.
Lemma lem193710 (a : Prop) (b : Prop) : (a -> b) = (term117 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem193711 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term119 _3912 _3913 _3910 _3911) = (term120 _3912 _3913 _3910 _3911).
Proof. exact (@lem193710 (_3910 = _3912) (term118 _3912 _3913 _3910 _3911)). Qed.
Lemma lem193712 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : term120 _3912 _3913 _3910 _3911.
Proof. exact (EQ_MP (@lem193711 _3912 _3913 _3910 _3911) (@lem193708 _3912 _3913 _3910 _3911)). Qed.
Lemma lem193753 (x : nat) (y : nat) (z : nat) : term121 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem193755 (_3900 : nat) (h1 : term17) : (S _3900) = (term34 _3900).
Proof. exact (EQ_MP (@lem193634 _3900) (@lem193633 _3900 h1)). Qed.
Lemma lem193756 (a : nat) (h1 : term17) : (S a) = (term34 a).
Proof. exact (@lem193755 a h1). Qed.
Lemma lem193757 (a : nat) (h1 : term17) : term122 a.
Proof. exact (fun h0 : term123 a => @lem193756 a h1). Qed.
Lemma lem193759 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem193760 (a : nat) : (term122 a) = ((S a) = (term34 a)).
Proof. exact (@lem193759 ((S a) = (term34 a))). Qed.
Lemma lem193761 (a : nat) (h1 : term17) : (S a) = (term34 a).
Proof. exact (EQ_MP (@lem193760 a) (@lem193757 a h1)). Qed.
Lemma lem193763 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem193764 (a : nat) : (S a) = (S a).
Proof. exact (@lem193763 (S a)). Qed.
Lemma lem193765 (a : nat) : term125 a.
Proof. exact (fun h0 : term126 a => @lem193764 a). Qed.
Lemma lem193767 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem193768 (a : nat) : (term125 a) = ((S a) = (S a)).
Proof. exact (@lem193767 ((S a) = (S a))). Qed.
Lemma lem193769 (a : nat) : (S a) = (S a).
Proof. exact (EQ_MP (@lem193768 a) (@lem193765 a)). Qed.
Lemma lem193787 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem193788 (y : nat) (x : nat) (z : nat) : (term127 x y z) = (term128 y x z).
Proof. exact (@lem193787 (y = z) (term129 x z)). Qed.
Lemma lem193798 (x : nat) (y : nat) : (term130 x y) = (term130 x y).
Proof. exact (eq_refl (term130 x y)). Qed.
Lemma lem193799 (y : nat) (x : nat) (z : nat) : (term121 x y z) = (term131 y x z).
Proof. exact (MK_COMB (@lem193798 x y) (@lem193788 y x z)). Qed.
Lemma lem193803 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem193804 (y : nat) (x : nat) (z : nat) : (term131 y x z) = (term132 y x z).
Proof. exact (@lem193803 (y = z) (term129 x y) (term129 x z)). Qed.
Lemma lem193826 (y : nat) (x : nat) (z : nat) : (term121 x y z) = (term132 y x z).
Proof. exact (TRANS (@lem193799 y x z) (@lem193804 y x z)). Qed.
Lemma lem193827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem193828 (y : nat) (x : nat) (z : nat) : (term133 x y z) = (term134 y x z).
Proof. exact (MK_COMB (@lem193827) (@lem193826 y x z)). Qed.
Lemma lem193850 (y : nat) (x : nat) (z : nat) : (term132 y x z) = (term132 y x z).
Proof. exact (eq_refl (term132 y x z)). Qed.
Lemma lem193851 (y : nat) (x : nat) (z : nat) : ((term121 x y z) = (term132 y x z)) = ((term132 y x z) = (term132 y x z)).
Proof. exact (MK_COMB (@lem193828 y x z) (@lem193850 y x z)). Qed.
Lemma lem193853 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem193854 (x : Prop) : (x = x) = True.
Proof. exact (@lem193853 Prop x). Qed.
Lemma lem193855 (y : nat) (x : nat) (z : nat) : ((term132 y x z) = (term132 y x z)) = True.
Proof. exact (@lem193854 (term132 y x z)). Qed.
Lemma lem193856 (y : nat) (x : nat) (z : nat) : ((term121 x y z) = (term132 y x z)) = True.
Proof. exact (TRANS (@lem193851 y x z) (@lem193855 y x z)). Qed.
Lemma lem193857 (y : nat) (x : nat) (z : nat) : True = ((term121 x y z) = (term132 y x z)).
Proof. exact (SYM (@lem193856 y x z)). Qed.
Lemma lem193858 (y : nat) (x : nat) (z : nat) : (term121 x y z) = (term132 y x z).
Proof. exact (EQ_MP (@lem193857 y x z) (@lem0)). Qed.
Lemma lem193859 (y : nat) (x : nat) (z : nat) : term132 y x z.
Proof. exact (EQ_MP (@lem193858 y x z) (@lem193753 x y z)). Qed.
Lemma lem193861 (b : Prop) (a : Prop) : (a \/ b) = (term135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem193862 (x : nat) (y : nat) (z : nat) : (term132 y x z) = (term136 x y z).
Proof. exact (@lem193861 (term137 y x z) (y = z)). Qed.
Lemma lem193864 (a : Prop) (b : Prop) : (term138 a b) = (term139 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem193865 (y : nat) (x : nat) (z : nat) : (term140 y x z) = (term141 y x z).
Proof. exact (@lem193864 (term129 x y) (term129 x z)). Qed.
Lemma lem193867 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem193868 (x : nat) (y : nat) : (term143 x y) = (x = y).
Proof. exact (@lem193867 (x = y)). Qed.
Lemma lem193869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem193870 (x : nat) (y : nat) : (term144 x y) = (term145 x y).
Proof. exact (MK_COMB (@lem193869) (@lem193868 x y)). Qed.
Lemma lem193872 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem193873 (x : nat) (z : nat) : (term143 x z) = (x = z).
Proof. exact (@lem193872 (x = z)). Qed.
Lemma lem193874 (y : nat) (x : nat) (z : nat) : (term141 y x z) = (term146 y x z).
Proof. exact (MK_COMB (@lem193870 x y) (@lem193873 x z)). Qed.
Lemma lem193875 (y : nat) (x : nat) (z : nat) : (term140 y x z) = (term146 y x z).
Proof. exact (TRANS (@lem193865 y x z) (@lem193874 y x z)). Qed.
Lemma lem193876 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem193877 (y : nat) (x : nat) (z : nat) : (term147 y x z) = (term148 y x z).
Proof. exact (MK_COMB (@lem193876) (@lem193875 y x z)). Qed.
Lemma lem193878 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem193879 (x : nat) (y : nat) (z : nat) : (term136 x y z) = (term149 x y z).
Proof. exact (MK_COMB (@lem193877 y x z) (@lem193878 y z)). Qed.
Lemma lem193880 (x : nat) (y : nat) (z : nat) : (term132 y x z) = (term149 x y z).
Proof. exact (TRANS (@lem193862 x y z) (@lem193879 x y z)). Qed.
Lemma lem193882 (a : nat) (h1 : term17) : term150 a.
Proof. exact (conj (@lem193761 a h1) (@lem193769 a)). Qed.
Lemma lem193884 (x : nat) (y : nat) (z : nat) : term149 x y z.
Proof. exact (EQ_MP (@lem193880 x y z) (@lem193859 y x z)). Qed.
Lemma lem193885 (a : nat) : term151 a.
Proof. exact (@lem193884 (S a) (term34 a) (S a)). Qed.
Lemma lem193888 (a : nat) (h1 : term17) : (term34 a) = (S a).
Proof. exact (@lem193885 a (@lem193882 a h1)). Qed.
Lemma lem193889 (a : nat) (h1 : term17) : term152 a.
Proof. exact (fun h0 : term153 a => @lem193888 a h1). Qed.
Lemma lem193891 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem193892 (a : nat) : (term152 a) = ((term34 a) = (S a)).
Proof. exact (@lem193891 ((term34 a) = (S a))). Qed.
Lemma lem193893 (a : nat) (h1 : term17) : (term34 a) = (S a).
Proof. exact (EQ_MP (@lem193892 a) (@lem193889 a h1)). Qed.
Lemma lem193895 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem193896 (b : nat) : b = b.
Proof. exact (@lem193895 b). Qed.
Lemma lem193897 (b : nat) : term154 b.
Proof. exact (fun h0 : term155 b => @lem193896 b). Qed.
Lemma lem193899 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem193900 (b : nat) : (term154 b) = (b = b).
Proof. exact (@lem193899 (b = b)). Qed.
Lemma lem193901 (b : nat) : b = b.
Proof. exact (EQ_MP (@lem193900 b) (@lem193897 b)). Qed.
Lemma lem193903 (_3899 : nat) (h1 : term42) : Peano.le _3899 _3899.
Proof. exact (EQ_MP (@lem193631 _3899) (@lem193630 _3899 h1)). Qed.
Lemma lem193904 (a : nat) (h1 : term42) : Peano.le a a.
Proof. exact (@lem193903 a h1). Qed.
Lemma lem193905 (a : nat) (h1 : term42) : term156 a.
Proof. exact (fun h0 : term157 a => @lem193904 a h1). Qed.
Lemma lem193907 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem193908 (a : nat) : (term156 a) = (Peano.le a a).
Proof. exact (@lem193907 (Peano.le a a)). Qed.
Lemma lem193909 (a : nat) (h1 : term42) : Peano.le a a.
Proof. exact (EQ_MP (@lem193908 a) (@lem193905 a h1)). Qed.
Lemma lem193915 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem193916 (b : nat) (_3905 : nat) (a : nat) : (term47 a _3905 b) = (term158 b _3905 a).
Proof. exact (@lem193915 (term48 _3905 b) (term159 _3905 a)). Qed.
Lemma lem193922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem193923 (b : nat) (_3905 : nat) (a : nat) : (term160 a _3905 b) = (term161 b _3905 a).
Proof. exact (MK_COMB (@lem193922) (@lem193916 b _3905 a)). Qed.
Lemma lem193929 (b : nat) (_3905 : nat) (a : nat) : (term158 b _3905 a) = (term158 b _3905 a).
Proof. exact (eq_refl (term158 b _3905 a)). Qed.
Lemma lem193930 (b : nat) (_3905 : nat) (a : nat) : ((term47 a _3905 b) = (term158 b _3905 a)) = ((term158 b _3905 a) = (term158 b _3905 a)).
Proof. exact (MK_COMB (@lem193923 b _3905 a) (@lem193929 b _3905 a)). Qed.
Lemma lem193932 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem193933 (x : Prop) : (x = x) = True.
Proof. exact (@lem193932 Prop x). Qed.
Lemma lem193934 (b : nat) (_3905 : nat) (a : nat) : ((term158 b _3905 a) = (term158 b _3905 a)) = True.
Proof. exact (@lem193933 (term158 b _3905 a)). Qed.
Lemma lem193935 (b : nat) (_3905 : nat) (a : nat) : ((term47 a _3905 b) = (term158 b _3905 a)) = True.
Proof. exact (TRANS (@lem193930 b _3905 a) (@lem193934 b _3905 a)). Qed.
Lemma lem193936 (b : nat) (_3905 : nat) (a : nat) : True = ((term47 a _3905 b) = (term158 b _3905 a)).
Proof. exact (SYM (@lem193935 b _3905 a)). Qed.
Lemma lem193937 (b : nat) (_3905 : nat) (a : nat) : (term47 a _3905 b) = (term158 b _3905 a).
Proof. exact (EQ_MP (@lem193936 b _3905 a) (@lem0)). Qed.
Lemma lem193938 (_3905 : nat) (a : nat) (b : nat) (h1 : term10 a b) : term158 b _3905 a.
Proof. exact (EQ_MP (@lem193937 b _3905 a) (@lem193672 _3905 a b h1)). Qed.
Lemma lem193940 (b : Prop) (a : Prop) : (a \/ b) = (term135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem193941 (a : nat) (_3905 : nat) (b : nat) : (term158 b _3905 a) = (term162 a _3905 b).
Proof. exact (@lem193940 (term159 _3905 a) (term48 _3905 b)). Qed.
Lemma lem193943 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem193944 (_3905 : nat) (a : nat) : (term163 _3905 a) = (Peano.le _3905 a).
Proof. exact (@lem193943 (Peano.le _3905 a)). Qed.
Lemma lem193945 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem193946 (_3905 : nat) (a : nat) : (term164 _3905 a) = (term165 _3905 a).
Proof. exact (MK_COMB (@lem193945) (@lem193944 _3905 a)). Qed.
Lemma lem193947 (_3905 : nat) (b : nat) : (term48 _3905 b) = (term48 _3905 b).
Proof. exact (eq_refl (term48 _3905 b)). Qed.
Lemma lem193948 (a : nat) (_3905 : nat) (b : nat) : (term162 a _3905 b) = (term43 a _3905 b).
Proof. exact (MK_COMB (@lem193946 _3905 a) (@lem193947 _3905 b)). Qed.
Lemma lem193949 (a : nat) (_3905 : nat) (b : nat) : (term158 b _3905 a) = (term43 a _3905 b).
Proof. exact (TRANS (@lem193941 a _3905 b) (@lem193948 a _3905 b)). Qed.
Lemma lem193952 (_3905 : nat) (a : nat) (b : nat) (h1 : term10 a b) : term43 a _3905 b.
Proof. exact (EQ_MP (@lem193949 a _3905 b) (@lem193938 _3905 a b h1)). Qed.
Lemma lem193953 (a : nat) (b : nat) (h1 : term10 a b) : term166 a b.
Proof. exact (@lem193952 a a b h1). Qed.
Lemma lem193956 (a : nat) (b : nat) (h1 : term42) (h2 : term10 a b) : term48 a b.
Proof. exact (@lem193953 a b h2 (@lem193909 a h1)). Qed.
Lemma lem193957 (a : nat) (b : nat) (h1 : term42) (h2 : term10 a b) : term167 a b.
Proof. exact (fun h0 : term168 a b => @lem193956 a b h1 h2). Qed.
Lemma lem193959 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem193960 (a : nat) (b : nat) : (term167 a b) = (term48 a b).
Proof. exact (@lem193959 (term48 a b)). Qed.
Lemma lem193961 (a : nat) (b : nat) (h1 : term42) (h2 : term10 a b) : term48 a b.
Proof. exact (EQ_MP (@lem193960 a b) (@lem193957 a b h1 h2)). Qed.
Lemma lem193979 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem193980 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term118 _3912 _3913 _3910 _3911) = (term169 _3912 _3913 _3910 _3911).
Proof. exact (@lem193979 (Peano.le _3912 _3913) (term129 _3911 _3913) (term159 _3910 _3911)). Qed.
Lemma lem193994 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem193995 (_3910 : nat) (_3911 : nat) (_3913 : nat) : (term170 _3913 _3910 _3911) = (term171 _3910 _3911 _3913).
Proof. exact (@lem193994 (term159 _3910 _3911) (term129 _3911 _3913)). Qed.
Lemma lem194003 (_3912 : nat) (_3913 : nat) : (term172 _3912 _3913) = (term172 _3912 _3913).
Proof. exact (eq_refl (term172 _3912 _3913)). Qed.
Lemma lem194004 (_3912 : nat) (_3910 : nat) (_3911 : nat) (_3913 : nat) : (term169 _3912 _3913 _3910 _3911) = (term173 _3912 _3910 _3911 _3913).
Proof. exact (MK_COMB (@lem194003 _3912 _3913) (@lem193995 _3910 _3911 _3913)). Qed.
Lemma lem194015 (_3912 : nat) (_3910 : nat) (_3911 : nat) (_3913 : nat) : (term118 _3912 _3913 _3910 _3911) = (term173 _3912 _3910 _3911 _3913).
Proof. exact (TRANS (@lem193980 _3912 _3913 _3910 _3911) (@lem194004 _3912 _3910 _3911 _3913)). Qed.
Lemma lem194016 (_3910 : nat) (_3912 : nat) : (term130 _3910 _3912) = (term130 _3910 _3912).
Proof. exact (eq_refl (term130 _3910 _3912)). Qed.
Lemma lem194017 (_3912 : nat) (_3910 : nat) (_3911 : nat) (_3913 : nat) : (term120 _3912 _3913 _3910 _3911) = (term174 _3912 _3910 _3911 _3913).
Proof. exact (MK_COMB (@lem194016 _3910 _3912) (@lem194015 _3912 _3910 _3911 _3913)). Qed.
Lemma lem194021 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem194022 (_3912 : nat) (_3910 : nat) (_3911 : nat) (_3913 : nat) : (term174 _3912 _3910 _3911 _3913) = (term175 _3912 _3910 _3911 _3913).
Proof. exact (@lem194021 (Peano.le _3912 _3913) (term129 _3910 _3912) (term171 _3910 _3911 _3913)). Qed.
Lemma lem194036 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem194037 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : (term176 _3912 _3910 _3911 _3913) = (term177 _3910 _3912 _3911 _3913).
Proof. exact (@lem194036 (term159 _3910 _3911) (term129 _3910 _3912) (term129 _3911 _3913)). Qed.
Lemma lem194057 (_3912 : nat) (_3913 : nat) : (term172 _3912 _3913) = (term172 _3912 _3913).
Proof. exact (eq_refl (term172 _3912 _3913)). Qed.
Lemma lem194058 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : (term175 _3912 _3910 _3911 _3913) = (term178 _3910 _3912 _3911 _3913).
Proof. exact (MK_COMB (@lem194057 _3912 _3913) (@lem194037 _3910 _3912 _3911 _3913)). Qed.
Lemma lem194069 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : (term174 _3912 _3910 _3911 _3913) = (term178 _3910 _3912 _3911 _3913).
Proof. exact (TRANS (@lem194022 _3912 _3910 _3911 _3913) (@lem194058 _3910 _3912 _3911 _3913)). Qed.
Lemma lem194070 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : (term120 _3912 _3913 _3910 _3911) = (term178 _3910 _3912 _3911 _3913).
Proof. exact (TRANS (@lem194017 _3912 _3910 _3911 _3913) (@lem194069 _3910 _3912 _3911 _3913)). Qed.
Lemma lem194071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem194072 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : (term179 _3912 _3913 _3910 _3911) = (term180 _3910 _3912 _3911 _3913).
Proof. exact (MK_COMB (@lem194071) (@lem194070 _3910 _3912 _3911 _3913)). Qed.
Lemma lem194098 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem194099 (_3910 : nat) (_3911 : nat) (_3913 : nat) : (term170 _3913 _3910 _3911) = (term171 _3910 _3911 _3913).
Proof. exact (@lem194098 (term159 _3910 _3911) (term129 _3911 _3913)). Qed.
Lemma lem194107 (_3910 : nat) (_3912 : nat) : (term130 _3910 _3912) = (term130 _3910 _3912).
Proof. exact (eq_refl (term130 _3910 _3912)). Qed.
Lemma lem194108 (_3912 : nat) (_3910 : nat) (_3911 : nat) (_3913 : nat) : (term181 _3912 _3913 _3910 _3911) = (term176 _3912 _3910 _3911 _3913).
Proof. exact (MK_COMB (@lem194107 _3910 _3912) (@lem194099 _3910 _3911 _3913)). Qed.
Lemma lem194112 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem194113 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : (term176 _3912 _3910 _3911 _3913) = (term177 _3910 _3912 _3911 _3913).
Proof. exact (@lem194112 (term159 _3910 _3911) (term129 _3910 _3912) (term129 _3911 _3913)). Qed.
Lemma lem194133 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : (term181 _3912 _3913 _3910 _3911) = (term177 _3910 _3912 _3911 _3913).
Proof. exact (TRANS (@lem194108 _3912 _3910 _3911 _3913) (@lem194113 _3910 _3912 _3911 _3913)). Qed.
Lemma lem194134 (_3912 : nat) (_3913 : nat) : (term172 _3912 _3913) = (term172 _3912 _3913).
Proof. exact (eq_refl (term172 _3912 _3913)). Qed.
Lemma lem194135 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : (term182 _3912 _3913 _3910 _3911) = (term178 _3910 _3912 _3911 _3913).
Proof. exact (MK_COMB (@lem194134 _3912 _3913) (@lem194133 _3910 _3912 _3911 _3913)). Qed.
Lemma lem194146 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : ((term120 _3912 _3913 _3910 _3911) = (term182 _3912 _3913 _3910 _3911)) = ((term178 _3910 _3912 _3911 _3913) = (term178 _3910 _3912 _3911 _3913)).
Proof. exact (MK_COMB (@lem194072 _3910 _3912 _3911 _3913) (@lem194135 _3910 _3912 _3911 _3913)). Qed.
Lemma lem194148 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem194149 (x : Prop) : (x = x) = True.
Proof. exact (@lem194148 Prop x). Qed.
Lemma lem194150 (_3910 : nat) (_3912 : nat) (_3911 : nat) (_3913 : nat) : ((term178 _3910 _3912 _3911 _3913) = (term178 _3910 _3912 _3911 _3913)) = True.
Proof. exact (@lem194149 (term178 _3910 _3912 _3911 _3913)). Qed.
Lemma lem194151 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : ((term120 _3912 _3913 _3910 _3911) = (term182 _3912 _3913 _3910 _3911)) = True.
Proof. exact (TRANS (@lem194146 _3910 _3912 _3911 _3913) (@lem194150 _3910 _3912 _3911 _3913)). Qed.
Lemma lem194152 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : True = ((term120 _3912 _3913 _3910 _3911) = (term182 _3912 _3913 _3910 _3911)).
Proof. exact (SYM (@lem194151 _3912 _3913 _3910 _3911)). Qed.
Lemma lem194153 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term120 _3912 _3913 _3910 _3911) = (term182 _3912 _3913 _3910 _3911).
Proof. exact (EQ_MP (@lem194152 _3912 _3913 _3910 _3911) (@lem0)). Qed.
Lemma lem194154 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : term182 _3912 _3913 _3910 _3911.
Proof. exact (EQ_MP (@lem194153 _3912 _3913 _3910 _3911) (@lem193712 _3912 _3913 _3910 _3911)). Qed.
Lemma lem194156 (b : Prop) (a : Prop) : (a \/ b) = (term135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem194157 (_3910 : nat) (_3911 : nat) (_3912 : nat) (_3913 : nat) : (term182 _3912 _3913 _3910 _3911) = (term183 _3910 _3911 _3912 _3913).
Proof. exact (@lem194156 (term181 _3912 _3913 _3910 _3911) (Peano.le _3912 _3913)). Qed.
Lemma lem194159 (a : Prop) (b : Prop) : (term138 a b) = (term139 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem194160 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term184 _3912 _3913 _3910 _3911) = (term185 _3912 _3913 _3910 _3911).
Proof. exact (@lem194159 (term129 _3910 _3912) (term170 _3913 _3910 _3911)). Qed.
Lemma lem194162 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem194163 (_3910 : nat) (_3912 : nat) : (term143 _3910 _3912) = (_3910 = _3912).
Proof. exact (@lem194162 (_3910 = _3912)). Qed.
Lemma lem194164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem194165 (_3910 : nat) (_3912 : nat) : (term144 _3910 _3912) = (term145 _3910 _3912).
Proof. exact (MK_COMB (@lem194164) (@lem194163 _3910 _3912)). Qed.
Lemma lem194167 (a : Prop) (b : Prop) : (term138 a b) = (term139 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem194168 (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term186 _3913 _3910 _3911) = (term187 _3913 _3910 _3911).
Proof. exact (@lem194167 (term129 _3911 _3913) (term159 _3910 _3911)). Qed.
Lemma lem194170 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem194171 (_3911 : nat) (_3913 : nat) : (term143 _3911 _3913) = (_3911 = _3913).
Proof. exact (@lem194170 (_3911 = _3913)). Qed.
Lemma lem194172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem194173 (_3911 : nat) (_3913 : nat) : (term144 _3911 _3913) = (term145 _3911 _3913).
Proof. exact (MK_COMB (@lem194172) (@lem194171 _3911 _3913)). Qed.
Lemma lem194175 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem194176 (_3910 : nat) (_3911 : nat) : (term163 _3910 _3911) = (Peano.le _3910 _3911).
Proof. exact (@lem194175 (Peano.le _3910 _3911)). Qed.
Lemma lem194177 (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term187 _3913 _3910 _3911) = (term188 _3913 _3910 _3911).
Proof. exact (MK_COMB (@lem194173 _3911 _3913) (@lem194176 _3910 _3911)). Qed.
Lemma lem194178 (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term186 _3913 _3910 _3911) = (term188 _3913 _3910 _3911).
Proof. exact (TRANS (@lem194168 _3913 _3910 _3911) (@lem194177 _3913 _3910 _3911)). Qed.
Lemma lem194179 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term185 _3912 _3913 _3910 _3911) = (term189 _3912 _3913 _3910 _3911).
Proof. exact (MK_COMB (@lem194165 _3910 _3912) (@lem194178 _3913 _3910 _3911)). Qed.
Lemma lem194180 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term184 _3912 _3913 _3910 _3911) = (term189 _3912 _3913 _3910 _3911).
Proof. exact (TRANS (@lem194160 _3912 _3913 _3910 _3911) (@lem194179 _3912 _3913 _3910 _3911)). Qed.
Lemma lem194181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem194182 (_3912 : nat) (_3913 : nat) (_3910 : nat) (_3911 : nat) : (term190 _3912 _3913 _3910 _3911) = (term191 _3912 _3913 _3910 _3911).
Proof. exact (MK_COMB (@lem194181) (@lem194180 _3912 _3913 _3910 _3911)). Qed.
Lemma lem194183 (_3912 : nat) (_3913 : nat) : (Peano.le _3912 _3913) = (Peano.le _3912 _3913).
Proof. exact (eq_refl (Peano.le _3912 _3913)). Qed.
Lemma lem194184 (_3910 : nat) (_3911 : nat) (_3912 : nat) (_3913 : nat) : (term183 _3910 _3911 _3912 _3913) = (term192 _3910 _3911 _3912 _3913).
Proof. exact (MK_COMB (@lem194182 _3912 _3913 _3910 _3911) (@lem194183 _3912 _3913)). Qed.
Lemma lem194185 (_3910 : nat) (_3911 : nat) (_3912 : nat) (_3913 : nat) : (term182 _3912 _3913 _3910 _3911) = (term192 _3910 _3911 _3912 _3913).
Proof. exact (TRANS (@lem194157 _3910 _3911 _3912 _3913) (@lem194184 _3910 _3911 _3912 _3913)). Qed.
Lemma lem194187 (a : nat) (b : nat) (h1 : term42) (h2 : term10 a b) : term193 a b.
Proof. exact (conj (@lem193901 b) (@lem193961 a b h1 h2)). Qed.
Lemma lem194188 (a : nat) (b : nat) (h1 : term42) (h2 : term17) (h3 : term10 a b) : term194 a b.
Proof. exact (conj (@lem193893 a h2) (@lem194187 a b h1 h3)). Qed.
Lemma lem194190 (_3910 : nat) (_3911 : nat) (_3912 : nat) (_3913 : nat) : term192 _3910 _3911 _3912 _3913.
Proof. exact (EQ_MP (@lem194185 _3910 _3911 _3912 _3913) (@lem194154 _3912 _3913 _3910 _3911)). Qed.
Lemma lem194191 (a : nat) (b : nat) : term195 a b.
Proof. exact (@lem194190 (term34 a) b (S a) b). Qed.
Lemma lem194194 (a : nat) (b : nat) (h1 : term42) (h2 : term17) (h3 : term10 a b) : term36 a b.
Proof. exact (@lem194191 a b (@lem194188 a b h1 h2 h3)). Qed.
Lemma lem194195 (a : nat) (b : nat) (h1 : term42) (h2 : term17) (h3 : term10 a b) : term196 a b.
Proof. exact (fun h0 : term197 a b => @lem194194 a b h1 h2 h3). Qed.
Lemma lem194197 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem194198 (a : nat) (b : nat) : (term196 a b) = (term36 a b).
Proof. exact (@lem194197 (term36 a b)). Qed.
Lemma lem194199 (a : nat) (b : nat) (h1 : term42) (h2 : term17) (h3 : term10 a b) : term36 a b.
Proof. exact (EQ_MP (@lem194198 a b) (@lem194195 a b h1 h2 h3)). Qed.
Lemma lem194205 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem194206 (_3903 : nat) (_3904 : nat) : (term74 _3903 _3904) = (term198 _3903 _3904).
Proof. exact (@lem194205 (Peano.lt _3903 _3904) (term197 _3903 _3904)). Qed.
Lemma lem194212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem194213 (_3903 : nat) (_3904 : nat) : (term199 _3903 _3904) = (term200 _3903 _3904).
Proof. exact (MK_COMB (@lem194212) (@lem194206 _3903 _3904)). Qed.
Lemma lem194219 (_3903 : nat) (_3904 : nat) : (term198 _3903 _3904) = (term198 _3903 _3904).
Proof. exact (eq_refl (term198 _3903 _3904)). Qed.
Lemma lem194220 (_3903 : nat) (_3904 : nat) : ((term74 _3903 _3904) = (term198 _3903 _3904)) = ((term198 _3903 _3904) = (term198 _3903 _3904)).
Proof. exact (MK_COMB (@lem194213 _3903 _3904) (@lem194219 _3903 _3904)). Qed.
Lemma lem194222 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem194223 (x : Prop) : (x = x) = True.
Proof. exact (@lem194222 Prop x). Qed.
Lemma lem194224 (_3903 : nat) (_3904 : nat) : ((term198 _3903 _3904) = (term198 _3903 _3904)) = True.
Proof. exact (@lem194223 (term198 _3903 _3904)). Qed.
Lemma lem194225 (_3903 : nat) (_3904 : nat) : ((term74 _3903 _3904) = (term198 _3903 _3904)) = True.
Proof. exact (TRANS (@lem194220 _3903 _3904) (@lem194224 _3903 _3904)). Qed.
Lemma lem194226 (_3903 : nat) (_3904 : nat) : True = ((term74 _3903 _3904) = (term198 _3903 _3904)).
Proof. exact (SYM (@lem194225 _3903 _3904)). Qed.
Lemma lem194227 (_3903 : nat) (_3904 : nat) : (term74 _3903 _3904) = (term198 _3903 _3904).
Proof. exact (EQ_MP (@lem194226 _3903 _3904) (@lem0)). Qed.
Lemma lem194228 (_3903 : nat) (_3904 : nat) (h1 : term40) : term198 _3903 _3904.
Proof. exact (EQ_MP (@lem194227 _3903 _3904) (@lem193666 _3903 _3904 h1)). Qed.
Lemma lem194230 (b : Prop) (a : Prop) : (a \/ b) = (term135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem194231 (_3903 : nat) (_3904 : nat) : (term198 _3903 _3904) = (term201 _3903 _3904).
Proof. exact (@lem194230 (term197 _3903 _3904) (Peano.lt _3903 _3904)). Qed.
Lemma lem194233 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem194234 (_3903 : nat) (_3904 : nat) : (term202 _3903 _3904) = (term36 _3903 _3904).
Proof. exact (@lem194233 (term36 _3903 _3904)). Qed.
Lemma lem194235 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem194236 (_3903 : nat) (_3904 : nat) : (term203 _3903 _3904) = (term204 _3903 _3904).
Proof. exact (MK_COMB (@lem194235) (@lem194234 _3903 _3904)). Qed.
Lemma lem194237 (_3903 : nat) (_3904 : nat) : (Peano.lt _3903 _3904) = (Peano.lt _3903 _3904).
Proof. exact (eq_refl (Peano.lt _3903 _3904)). Qed.
Lemma lem194238 (_3903 : nat) (_3904 : nat) : (term201 _3903 _3904) = (term205 _3903 _3904).
Proof. exact (MK_COMB (@lem194236 _3903 _3904) (@lem194237 _3903 _3904)). Qed.
Lemma lem194239 (_3903 : nat) (_3904 : nat) : (term198 _3903 _3904) = (term205 _3903 _3904).
Proof. exact (TRANS (@lem194231 _3903 _3904) (@lem194238 _3903 _3904)). Qed.
Lemma lem194242 (_3903 : nat) (_3904 : nat) (h1 : term40) : term205 _3903 _3904.
Proof. exact (EQ_MP (@lem194239 _3903 _3904) (@lem194228 _3903 _3904 h1)). Qed.
Lemma lem194243 (a : nat) (b : nat) (h1 : term40) : term205 a b.
Proof. exact (@lem194242 a b h1). Qed.
Lemma lem194246 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : Peano.lt a b.
Proof. exact (@lem194243 a b h1 (@lem194199 a b h2 h3 h4)). Qed.
Lemma lem194247 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : term206 a b.
Proof. exact (fun h0 : term51 a b => @lem194246 a b h1 h2 h3 h4). Qed.
Lemma lem194249 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem194250 (a : nat) (b : nat) : (term206 a b) = (Peano.lt a b).
Proof. exact (@lem194249 (Peano.lt a b)). Qed.
Lemma lem194251 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : Peano.lt a b.
Proof. exact (EQ_MP (@lem194250 a b) (@lem194247 a b h1 h2 h3 h4)). Qed.
Lemma lem194254 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem194256 (a : nat) (b : nat) : (term51 a b) = (term207 a b).
Proof. exact (@lem194254 (Peano.lt a b)). Qed.
Lemma lem194259 (a : nat) (b : nat) (h1 : term10 a b) : term207 a b.
Proof. exact (EQ_MP (@lem194256 a b) (@lem193674 a b h1)). Qed.
Lemma lem194262 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : False.
Proof. exact (@lem194259 a b h4 (@lem194251 a b h1 h2 h3 h4)). Qed.
Lemma lem194263 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : term208.
Proof. exact (fun h0 : ~ False => @lem194262 a b h1 h2 h3 h4). Qed.
Lemma lem194265 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem194266 : term208 = False.
Proof. exact (@lem194265 False). Qed.
Lemma lem194267 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : False.
Proof. exact (EQ_MP (@lem194266) (@lem194263 a b h1 h2 h3 h4)). Qed.
Lemma lem194268 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : term17 = False.
Proof. exact (prop_ext (fun h5 : term17 => @lem194267 a b h1 h2 h3 h4) (fun h5 : False => @lem193580 h3)). Qed.
Lemma lem194269 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : False.
Proof. exact (EQ_MP (@lem194268 a b h1 h2 h3 h4) (@lem193580 h3)). Qed.
Lemma lem194270 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : term42 = False.
Proof. exact (prop_ext (fun h5 : term42 => @lem194269 a b h1 h2 h3 h4) (fun h5 : False => @lem193573 h2)). Qed.
Lemma lem194271 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : False.
Proof. exact (EQ_MP (@lem194270 a b h1 h2 h3 h4) (@lem193573 h2)). Qed.
Lemma lem194272 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : term17 = False.
Proof. exact (prop_ext (fun h5 : term17 => @lem194271 a b h1 h2 h3 h4) (fun h5 : False => @lem193562 h3)). Qed.
Lemma lem194273 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : False.
Proof. exact (EQ_MP (@lem194272 a b h1 h2 h3 h4) (@lem193562 h3)). Qed.
Lemma lem194274 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : term42 = False.
Proof. exact (prop_ext (fun h5 : term42 => @lem194273 a b h1 h2 h3 h4) (fun h5 : False => @lem193493 h2)). Qed.
Lemma lem194275 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : False.
Proof. exact (EQ_MP (@lem194274 a b h1 h2 h3 h4) (@lem193493 h2)). Qed.
Lemma lem194276 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : term17 = False.
Proof. exact (prop_ext (fun h5 : term17 => @lem194275 a b h1 h2 h3 h4) (fun h5 : False => @lem193447 h3)). Qed.
Lemma lem194277 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : False.
Proof. exact (EQ_MP (@lem194276 a b h1 h2 h3 h4) (@lem193447 h3)). Qed.
Lemma lem194278 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : term42 = False.
Proof. exact (prop_ext (fun h5 : term42 => @lem194277 a b h1 h2 h3 h4) (fun h5 : False => @lem193147 h2)). Qed.
Lemma lem194279 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term17) (h4 : term10 a b) : False.
Proof. exact (EQ_MP (@lem194278 a b h1 h2 h3 h4) (@lem193147 h2)). Qed.
Lemma lem194280 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term10 a b) : term15.
Proof. exact (fun h0 : term17 => @lem194279 a b h1 h2 h0 h3). Qed.
Lemma lem194281 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem194282 (a : nat) (b : nat) (h1 : term40) (h2 : term42) (h3 : term10 a b) : term16.
Proof. exact (EQ_MP (@lem194281) (@lem194280 a b h1 h2 h3)). Qed.
Lemma lem194283 (a : nat) (b : nat) (h1 : term42) (h2 : term10 a b) : term20.
Proof. exact (fun h0 : term40 => @lem194282 a b h0 h1 h2). Qed.
Lemma lem194284 (a : nat) (b : nat) (h1 : term10 a b) : term23.
Proof. exact (fun h0 : term42 => @lem194283 a b h0 h1). Qed.
Lemma lem194285 (a : nat) (b : nat) : term25 a b.
Proof. exact (fun h0 : term10 a b => @lem194284 a b h0). Qed.
Lemma lem194290 (b : nat) : term29 b.
Proof. exact (fun a : nat => @lem194285 a b). Qed.
Lemma lem194295 : term33.
Proof. exact (fun b : nat => @lem194290 b). Qed.
Lemma lem194296 : term32.
Proof. exact (EQ_MP (@lem193061) (@lem194295)). Qed.
Lemma lem194297 (b : nat) : term209 b.
Proof. exact (@lem194296 b). Qed.
Lemma lem194298 (b : nat) : (term209 b) = (term28 b).
Proof. exact (eq_refl (term209 b)). Qed.
Lemma lem194299 (b : nat) : term28 b.
Proof. exact (EQ_MP (@lem194298 b) (@lem194297 b)). Qed.
Lemma lem194300 (b : nat) (a : nat) : term210 b a.
Proof. exact (@lem194299 b a). Qed.
Lemma lem194301 (a : nat) (b : nat) : (term210 b a) = (term11 a b).
Proof. exact (eq_refl (term210 b a)). Qed.
Lemma lem194302 (a : nat) (b : nat) : term11 a b.
Proof. exact (EQ_MP (@lem194301 a b) (@lem194300 b a)). Qed.
Lemma lem194304 (a : nat) (b : nat) : term11 a b.
Proof. exact (@lem192884 a b (@lem194302 a b)). Qed.
Lemma lem194305 (a : nat) (b : nat) (h1 : term10 a b) : term22.
Proof. exact (@lem194304 a b (@lem192869 a b h1)). Qed.
Lemma lem194306 (a : nat) (b : nat) (h1 : term10 a b) : term19.
Proof. exact (@lem194305 a b h1 (@lem91603)). Qed.
Lemma lem194307 (a : nat) (b : nat) (h1 : term10 a b) : term15.
Proof. exact (@lem194306 a b h1 (@lem91144)). Qed.
Lemma lem194308 (a : nat) (b : nat) (h1 : term10 a b) : False.
Proof. exact (@lem194307 a b h1 (@lem80621)). Qed.
Lemma lem194309 (a : nat) (b : nat) (h1 : term10 a b) : (term10 a b) = False.
Proof. exact (prop_ext (fun h2 : term10 a b => @lem194308 a b h1) (fun h2 : False => @lem192869 a b h1)). Qed.
Lemma lem194310 (a : nat) (b : nat) (h1 : term10 a b) : False.
Proof. exact (EQ_MP (@lem194309 a b h1) (@lem192869 a b h1)). Qed.
Lemma lem194311 (a : nat) (b : nat) : term9 a b.
Proof. exact (fun h0 : term10 a b => @lem194310 a b h0). Qed.
Lemma lem194312 (a : nat) (b : nat) : term8 a b.
Proof. exact (EQ_MP (@lem192868 a b) (@lem194311 a b)). Qed.
Lemma lem194313 (a : nat) (b : nat) (h1 : term8 a b) : term8 a b.
Proof. exact (h1). Qed.
Lemma lem194314 (a : nat) (b : nat) (h1 : term45 a b) : term45 a b.
Proof. exact (h1). Qed.
Lemma lem194315 (a : nat) (b : nat) (h1 : term45 a b) (h2 : term8 a b) : Peano.lt a b.
Proof. exact (@lem194313 a b h2 (@lem194314 a b h1)). Qed.
Lemma lem194316 (a : nat) (b : nat) (h1 : term45 a b) : term211 a b.
Proof. exact (fun h0 : term8 a b => @lem194315 a b h1 h0). Qed.
Lemma lem194317 (a : nat) (b : nat) (h1 : term8 a b) : term8 a b.
Proof. exact (h1). Qed.
Lemma lem194318 (a : nat) (b : nat) (h1 : term45 a b) (h2 : term8 a b) : Peano.lt a b.
Proof. exact (@lem194316 a b h1 (@lem194317 a b h2)). Qed.
Lemma lem194319 (a : nat) (b : nat) (h1 : term8 a b) : term8 a b.
Proof. exact (fun h0 : term45 a b => @lem194318 a b h0 h1). Qed.
Lemma lem194320 (a : nat) (b : nat) : term212 a b.
Proof. exact (fun h0 : term8 a b => @lem194319 a b h0). Qed.
Lemma lem194322 (m : nat) (p : nat) (n : nat) (h1 : term213 m p n) : term213 m p n.
Proof. exact (h1). Qed.
Lemma lem194323 (m : nat) (p : nat) (n : nat) (h1 : term214 m p n) : term214 m p n.
Proof. exact (h1). Qed.
Lemma lem194324 (p : nat) (h1 : term215 p) : term215 p.
Proof. exact (h1). Qed.
Lemma lem194326 (a : nat) (b : nat) : term8 a b.
Proof. exact (@lem194320 a b (@lem194312 a b)). Qed.
Lemma lem194327 (m : nat) (n : nat) (p : nat) : term216 m n p.
Proof. exact (@lem194326 (Nat.div m p) (Nat.div n p)). Qed.
Lemma lem194328 : term217.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem194329 : term218.
Proof. exact (proj2 (@lem194328)). Qed.
Lemma lem194330 : term219.
Proof. exact (proj2 (@lem194329)). Qed.
Lemma lem194346 : term220.
Proof. exact (proj1 (@lem194330)). Qed.
Lemma lem194347 (m : nat) : term221 m.
Proof. exact (@lem194346 m). Qed.
Lemma lem194348 (m : nat) : (term221 m) = ((term222 m) = m).
Proof. exact (eq_refl (term221 m)). Qed.
Lemma lem194362 (m : nat) : term223 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem194363 (m : nat) : (term223 m) = (term224 m).
Proof. exact (eq_refl (term223 m)). Qed.
Lemma lem194364 (m : nat) : term224 m.
Proof. exact (EQ_MP (@lem194363 m) (@lem194362 m)). Qed.
Lemma lem194365 (m : nat) (n : nat) : term225 m n.
Proof. exact (@lem194364 m n). Qed.
Lemma lem194366 (n : nat) (m : nat) : (term225 m n) = (term226 n m).
Proof. exact (eq_refl (term225 m n)). Qed.
Lemma lem194367 (n : nat) (m : nat) : term226 n m.
Proof. exact (EQ_MP (@lem194366 n m) (@lem194365 m n)). Qed.
Lemma lem194368 (n : nat) (m : nat) (p : nat) : term227 n m p.
Proof. exact (@lem194367 n m p). Qed.
Lemma lem194369 (n : nat) (m : nat) (p : nat) : (term227 n m p) = ((term228 m n p) = (term229 n m p)).
Proof. exact (eq_refl (term227 n m p)). Qed.
Lemma lem194371 (a : nat) : term230 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem194372 (a : nat) : (term230 a) = (term231 a).
Proof. exact (eq_refl (term230 a)). Qed.
Lemma lem194373 (a : nat) : term231 a.
Proof. exact (EQ_MP (@lem194372 a) (@lem194371 a)). Qed.
Lemma lem194374 (a : nat) (b : nat) : term232 a b.
Proof. exact (@lem194373 a b). Qed.
Lemma lem194375 (a : nat) (b : nat) : (term232 a b) = (term233 a b).
Proof. exact (eq_refl (term232 a b)). Qed.
Lemma lem194376 (a : nat) (b : nat) : term233 a b.
Proof. exact (EQ_MP (@lem194375 a b) (@lem194374 a b)). Qed.
Lemma lem194377 (a : nat) (b : nat) (n : nat) : term234 a b n.
Proof. exact (@lem194376 a b n). Qed.
Lemma lem194378 (a : nat) (n : nat) (b : nat) : (term234 a b n) = (term235 a n b).
Proof. exact (eq_refl (term234 a b n)). Qed.
Lemma lem194379 (a : nat) (n : nat) (b : nat) : term235 a n b.
Proof. exact (EQ_MP (@lem194378 a n b) (@lem194377 a b n)). Qed.
Lemma lem194380 (a : nat) (h1 : term215 a) : term215 a.
Proof. exact (h1). Qed.
Lemma lem194381 (n : nat) (b : nat) (a : nat) (h1 : term215 a) : (term236 n b a) = (term237 a n b).
Proof. exact (@lem194379 a n b (@lem194380 a h1)). Qed.
Lemma lem194387 (p : nat) : term238 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem194409 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term239 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem194410 (p : Prop) (q : Prop) (p' : Prop) : term240 p q p'.
Proof. exact (fun q' : Prop => @lem194409 p q p' q'). Qed.
Lemma lem194411 (p : Prop) (q : Prop) : term241 p q.
Proof. exact (fun p' : Prop => @lem194410 p q p'). Qed.
Lemma lem194412 (m : nat) (k : nat) (n : nat) (p : nat) : term242 m k n p.
Proof. exact (@lem194411 (term236 k m p) (term243 k n p)). Qed.
Lemma lem194413 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) : term244 m k n p p'.
Proof. exact (@lem194412 m k n p p'). Qed.
Lemma lem194414 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) : (term244 m k n p p') = (term245 m k n p p').
Proof. exact (eq_refl (term244 m k n p p')). Qed.
Lemma lem194415 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) : term245 m k n p p'.
Proof. exact (EQ_MP (@lem194414 m k n p p') (@lem194413 m k n p p')). Qed.
Lemma lem194416 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) (q' : Prop) : term246 m k n p p' q'.
Proof. exact (@lem194415 m k n p p' q'). Qed.
Lemma lem194417 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) (q' : Prop) : (term246 m k n p p' q') = (term247 m k n p p' q').
Proof. exact (eq_refl (term246 m k n p p' q')). Qed.
Lemma lem194418 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) (q' : Prop) : term247 m k n p p' q'.
Proof. exact (EQ_MP (@lem194417 m k n p p' q') (@lem194416 m k n p p' q')). Qed.
Lemma lem194420 (a : nat) (n : nat) (b : nat) : term235 a n b.
Proof. exact (fun h0 : term215 a => @lem194381 n b a h0). Qed.
Lemma lem194421 (p : nat) (k : nat) (m : nat) : term235 p k m.
Proof. exact (@lem194420 p k m). Qed.
Lemma lem194423 (p : nat) (h1 : term215 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem194387 p (@lem194324 p h1)). Qed.
Lemma lem194424 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem194425 (p : nat) (h1 : term215 p) : (term215 p) = (~ False).
Proof. exact (MK_COMB (@lem194424) (@lem194423 p h1)). Qed.
Lemma lem194427 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem194428 (p : nat) (h1 : term215 p) : (term215 p) = True.
Proof. exact (TRANS (@lem194425 p h1) (@lem194427)). Qed.
Lemma lem194429 (p : nat) (h1 : term215 p) : True = (term215 p).
Proof. exact (SYM (@lem194428 p h1)). Qed.
Lemma lem194430 (p : nat) (h1 : term215 p) : term215 p.
Proof. exact (EQ_MP (@lem194429 p h1) (@lem0)). Qed.
Lemma lem194431 (k : nat) (m : nat) (p : nat) (h1 : term215 p) : (term236 k m p) = (term237 p k m).
Proof. exact (@lem194421 p k m (@lem194430 p h1)). Qed.
Lemma lem194432 (n : nat) (p : nat) (k : nat) (m : nat) (q' : Prop) : term248 n p k m q'.
Proof. exact (@lem194418 m k n p (term237 p k m) q'). Qed.
Lemma lem194433 (n : nat) (k : nat) (m : nat) (q' : Prop) (p : nat) (h1 : term215 p) : term249 n p k m q'.
Proof. exact (@lem194432 n p k m q' (@lem194431 k m p h1)). Qed.
Lemma lem194438 (a : nat) (n : nat) (b : nat) : term235 a n b.
Proof. exact (fun h0 : term215 a => @lem194381 n b a h0). Qed.
Lemma lem194439 (p : nat) (k : nat) (n : nat) : term250 p k n.
Proof. exact (@lem194438 p (term34 k) n). Qed.
Lemma lem194441 (p : nat) (h1 : term215 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem194387 p (@lem194324 p h1)). Qed.
Lemma lem194442 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem194443 (p : nat) (h1 : term215 p) : (term215 p) = (~ False).
Proof. exact (MK_COMB (@lem194442) (@lem194441 p h1)). Qed.
Lemma lem194445 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem194446 (p : nat) (h1 : term215 p) : (term215 p) = True.
Proof. exact (TRANS (@lem194443 p h1) (@lem194445)). Qed.
Lemma lem194447 (p : nat) (h1 : term215 p) : True = (term215 p).
Proof. exact (SYM (@lem194446 p h1)). Qed.
Lemma lem194448 (p : nat) (h1 : term215 p) : term215 p.
Proof. exact (EQ_MP (@lem194447 p h1) (@lem0)). Qed.
Lemma lem194449 (k : nat) (n : nat) (p : nat) (h1 : term215 p) : (term243 k n p) = (term251 p k n).
Proof. exact (@lem194439 p k n (@lem194448 p h1)). Qed.
Lemma lem194451 (n : nat) (m : nat) (p : nat) : (term228 m n p) = (term229 n m p).
Proof. exact (EQ_MP (@lem194369 n m p) (@lem194368 n m p)). Qed.
Lemma lem194452 (k : nat) (p : nat) : (term252 p k) = (term253 k p).
Proof. exact (@lem194451 k p term254). Qed.
Lemma lem194454 (m : nat) : (term222 m) = m.
Proof. exact (EQ_MP (@lem194348 m) (@lem194347 m)). Qed.
Lemma lem194455 (p : nat) : (term222 p) = p.
Proof. exact (@lem194454 p). Qed.
Lemma lem194456 (p : nat) (k : nat) : (term255 p k) = (term255 p k).
Proof. exact (eq_refl (term255 p k)). Qed.
Lemma lem194457 (k : nat) (p : nat) : (term253 k p) = (term256 k p).
Proof. exact (MK_COMB (@lem194456 p k) (@lem194455 p)). Qed.
Lemma lem194458 (k : nat) (p : nat) : (term252 p k) = (term256 k p).
Proof. exact (TRANS (@lem194452 k p) (@lem194457 k p)). Qed.
Lemma lem194459 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem194460 (k : nat) (p : nat) : (term257 p k) = (term258 k p).
Proof. exact (MK_COMB (@lem194459) (@lem194458 k p)). Qed.
Lemma lem194461 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem194462 (k : nat) (p : nat) (n : nat) : (term251 p k n) = (term259 k p n).
Proof. exact (MK_COMB (@lem194460 k p) (@lem194461 n)). Qed.
Lemma lem194463 (k : nat) (n : nat) (p : nat) (h1 : term215 p) : (term243 k n p) = (term259 k p n).
Proof. exact (TRANS (@lem194449 k n p h1) (@lem194462 k p n)). Qed.
Lemma lem194464 (m : nat) (k : nat) (n : nat) (p : nat) (h1 : term215 p) : term260 m k p n.
Proof. exact (fun h0 : term237 p k m => @lem194463 k n p h1). Qed.
Lemma lem194465 (m : nat) (k : nat) (n : nat) (p : nat) (h1 : term215 p) : term261 m k p n.
Proof. exact (@lem194433 n k m (term259 k p n) p h1). Qed.
Lemma lem194466 (m : nat) (k : nat) (n : nat) (p : nat) (h1 : term215 p) : (term262 m k n p) = (term263 m k p n).
Proof. exact (@lem194465 m k n p h1 (@lem194464 m k n p h1)). Qed.
Lemma lem194490 (m : nat) (n : nat) (p : nat) (h1 : term215 p) : (term264 m n p) = (term265 m p n).
Proof. exact (fun_ext (fun k : nat => @lem194466 m k n p h1)). Qed.
Lemma lem194514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194515 (m : nat) (n : nat) (p : nat) (h1 : term215 p) : (term266 m n p) = (term267 m p n).
Proof. exact (MK_COMB (@lem194514) (@lem194490 m n p h1)). Qed.
Lemma lem194543 (m : nat) (n : nat) (p : nat) (h1 : term215 p) : (term267 m p n) = (term266 m n p).
Proof. exact (SYM (@lem194515 m n p h1)). Qed.
Lemma lem194545 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem194546 (m : nat) (p : nat) (n : nat) : (term267 m p n) = (term268 m p n).
Proof. exact (@lem194545 (term267 m p n)). Qed.
Lemma lem194547 (m : nat) (p : nat) (n : nat) : (term268 m p n) = (term267 m p n).
Proof. exact (SYM (@lem194546 m p n)). Qed.
Lemma lem194548 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) : term269 m p n.
Proof. exact (h1). Qed.
Lemma lem194551 (m : nat) (p : nat) (n : nat) (h1 : term270 m p n) : term270 m p n.
Proof. exact (h1). Qed.
Lemma lem194552 (m : nat) (p : nat) (n : nat) : term271 m p n.
Proof. exact (fun h0 : term270 m p n => @lem194551 m p n h0). Qed.
Lemma lem194553 (m : nat) (p : nat) (n : nat) (h1 : term271 m p n) : term271 m p n.
Proof. exact (h1). Qed.
Lemma lem194554 (m : nat) (p : nat) (n : nat) (h1 : term270 m p n) : term270 m p n.
Proof. exact (h1). Qed.
Lemma lem194555 (m : nat) (p : nat) (n : nat) (h1 : term270 m p n) (h2 : term271 m p n) : term270 m p n.
Proof. exact (@lem194553 m p n h2 (@lem194554 m p n h1)). Qed.
Lemma lem194556 (m : nat) (p : nat) (n : nat) (h1 : term270 m p n) : term272 m p n.
Proof. exact (fun h0 : term271 m p n => @lem194555 m p n h1 h0). Qed.
Lemma lem194557 (m : nat) (p : nat) (n : nat) (h1 : term271 m p n) : term271 m p n.
Proof. exact (h1). Qed.
Lemma lem194558 (m : nat) (p : nat) (n : nat) (h1 : term270 m p n) (h2 : term271 m p n) : term270 m p n.
Proof. exact (@lem194556 m p n h1 (@lem194557 m p n h2)). Qed.
Lemma lem194559 (m : nat) (p : nat) (n : nat) (h1 : term271 m p n) : term271 m p n.
Proof. exact (fun h0 : term270 m p n => @lem194558 m p n h0 h1). Qed.
Lemma lem194560 (m : nat) (p : nat) (n : nat) : term273 m p n.
Proof. exact (fun h0 : term271 m p n => @lem194559 m p n h0). Qed.
Lemma lem194563 (m : nat) (p : nat) (n : nat) : term271 m p n.
Proof. exact (@lem194560 m p n (@lem194552 m p n)). Qed.
Lemma lem194639 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem194640 : term274 = term275.
Proof. exact (@lem194639 term42). Qed.
Lemma lem194645 : term276 = term276.
Proof. exact (eq_refl term276). Qed.
Lemma lem194646 : term277 = term278.
Proof. exact (MK_COMB (@lem194645) (@lem194640)). Qed.
Lemma lem194649 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem194650 : term280 = term281.
Proof. exact (MK_COMB (@lem194649) (@lem194646)). Qed.
Lemma lem194653 : term282 = term282.
Proof. exact (eq_refl term282). Qed.
Lemma lem194654 : term283 = term284.
Proof. exact (MK_COMB (@lem194653) (@lem194650)). Qed.
Lemma lem194657 (m : nat) (p : nat) (n : nat) : (term285 m p n) = (term285 m p n).
Proof. exact (eq_refl (term285 m p n)). Qed.
Lemma lem194658 (m : nat) (p : nat) (n : nat) : (term286 m p n) = (term287 m p n).
Proof. exact (MK_COMB (@lem194657 m p n) (@lem194654)). Qed.
Lemma lem194661 (m : nat) (p : nat) (n : nat) : (term288 m p n) = (term288 m p n).
Proof. exact (eq_refl (term288 m p n)). Qed.
Lemma lem194662 (m : nat) (p : nat) (n : nat) : (term289 m p n) = (term290 m p n).
Proof. exact (MK_COMB (@lem194661 m p n) (@lem194658 m p n)). Qed.
Lemma lem194665 (p : nat) : (term291 p) = (term291 p).
Proof. exact (eq_refl (term291 p)). Qed.
Lemma lem194666 (m : nat) (p : nat) (n : nat) : (term270 m p n) = (term292 m p n).
Proof. exact (MK_COMB (@lem194665 p) (@lem194662 m p n)). Qed.
Lemma lem194669 (p : nat) (n : nat) : (term293 p n) = (term294 p n).
Proof. exact (fun_ext (fun m : nat => @lem194666 m p n)). Qed.
Lemma lem194670 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194671 (p : nat) (n : nat) : (term295 p n) = (term296 p n).
Proof. exact (MK_COMB (@lem194670) (@lem194669 p n)). Qed.
Lemma lem194676 (n : nat) : (term297 n) = (term298 n).
Proof. exact (fun_ext (fun p : nat => @lem194671 p n)). Qed.
Lemma lem194677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194678 (n : nat) : (term299 n) = (term300 n).
Proof. exact (MK_COMB (@lem194677) (@lem194676 n)). Qed.
Lemma lem194683 : term301 = term302.
Proof. exact (fun_ext (fun n : nat => @lem194678 n)). Qed.
Lemma lem194684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194693 : term303 = term304.
Proof. exact (MK_COMB (@lem194684) (@lem194683)). Qed.
Lemma lem194694 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem194695 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem194694 n)). Qed.
Lemma lem194696 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194697 : term42 = term42.
Proof. exact (MK_COMB (@lem194696) (@lem194695)). Qed.
Lemma lem194698 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem194699 : term275 = term275.
Proof. exact (MK_COMB (@lem194698) (@lem194697)). Qed.
Lemma lem194708 (n : nat) (m : nat) (p : nat) : (term305 n m p) = (term305 n m p).
Proof. exact (eq_refl (term305 n m p)). Qed.
Lemma lem194709 (n : nat) (m : nat) : (term306 n m) = (term306 n m).
Proof. exact (fun_ext (fun p : nat => @lem194708 n m p)). Qed.
Lemma lem194710 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194711 (n : nat) (m : nat) : (term307 n m) = (term307 n m).
Proof. exact (MK_COMB (@lem194710) (@lem194709 n m)). Qed.
Lemma lem194712 (m : nat) : (term308 m) = (term308 m).
Proof. exact (fun_ext (fun n : nat => @lem194711 n m)). Qed.
Lemma lem194713 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194714 (m : nat) : (term309 m) = (term309 m).
Proof. exact (MK_COMB (@lem194713) (@lem194712 m)). Qed.
Lemma lem194715 : term310 = term310.
Proof. exact (fun_ext (fun m : nat => @lem194714 m)). Qed.
Lemma lem194716 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194717 : term311 = term311.
Proof. exact (MK_COMB (@lem194716) (@lem194715)). Qed.
Lemma lem194718 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem194719 : term276 = term276.
Proof. exact (MK_COMB (@lem194718) (@lem194717)). Qed.
Lemma lem194720 : term278 = term278.
Proof. exact (MK_COMB (@lem194719) (@lem194699)). Qed.
Lemma lem194729 (m : nat) (n : nat) (p : nat) (q : nat) : (term312 m n p q) = (term312 m n p q).
Proof. exact (eq_refl (term312 m n p q)). Qed.
Lemma lem194730 (m : nat) (n : nat) (p : nat) : (term313 m n p) = (term313 m n p).
Proof. exact (fun_ext (fun q : nat => @lem194729 m n p q)). Qed.
Lemma lem194731 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194732 (m : nat) (n : nat) (p : nat) : (term314 m n p) = (term314 m n p).
Proof. exact (MK_COMB (@lem194731) (@lem194730 m n p)). Qed.
Lemma lem194733 (m : nat) (n : nat) : (term315 m n) = (term315 m n).
Proof. exact (fun_ext (fun p : nat => @lem194732 m n p)). Qed.
Lemma lem194734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194735 (m : nat) (n : nat) : (term316 m n) = (term316 m n).
Proof. exact (MK_COMB (@lem194734) (@lem194733 m n)). Qed.
Lemma lem194736 (m : nat) : (term317 m) = (term317 m).
Proof. exact (fun_ext (fun n : nat => @lem194735 m n)). Qed.
Lemma lem194737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194738 (m : nat) : (term318 m) = (term318 m).
Proof. exact (MK_COMB (@lem194737) (@lem194736 m)). Qed.
Lemma lem194739 : term319 = term319.
Proof. exact (fun_ext (fun m : nat => @lem194738 m)). Qed.
Lemma lem194740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194741 : term320 = term320.
Proof. exact (MK_COMB (@lem194740) (@lem194739)). Qed.
Lemma lem194742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem194743 : term279 = term279.
Proof. exact (MK_COMB (@lem194742) (@lem194741)). Qed.
Lemma lem194744 : term281 = term281.
Proof. exact (MK_COMB (@lem194743) (@lem194720)). Qed.
Lemma lem194745 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem194746 (m : nat) : (term321 m) = (term321 m).
Proof. exact (fun_ext (fun n : nat => @lem194745 n m)). Qed.
Lemma lem194747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194748 (m : nat) : (term322 m) = (term322 m).
Proof. exact (MK_COMB (@lem194747) (@lem194746 m)). Qed.
Lemma lem194749 : term323 = term323.
Proof. exact (fun_ext (fun m : nat => @lem194748 m)). Qed.
Lemma lem194750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194751 : term324 = term324.
Proof. exact (MK_COMB (@lem194750) (@lem194749)). Qed.
Lemma lem194752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem194753 : term282 = term282.
Proof. exact (MK_COMB (@lem194752) (@lem194751)). Qed.
Lemma lem194754 : term284 = term284.
Proof. exact (MK_COMB (@lem194753) (@lem194744)). Qed.
Lemma lem194759 (m : nat) (k : nat) (p : nat) (n : nat) : (term263 m k p n) = (term263 m k p n).
Proof. exact (eq_refl (term263 m k p n)). Qed.
Lemma lem194760 (m : nat) (p : nat) (n : nat) : (term265 m p n) = (term265 m p n).
Proof. exact (fun_ext (fun k : nat => @lem194759 m k p n)). Qed.
Lemma lem194761 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194762 (m : nat) (p : nat) (n : nat) : (term267 m p n) = (term267 m p n).
Proof. exact (MK_COMB (@lem194761) (@lem194760 m p n)). Qed.
Lemma lem194763 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem194764 (m : nat) (p : nat) (n : nat) : (term269 m p n) = (term269 m p n).
Proof. exact (MK_COMB (@lem194763) (@lem194762 m p n)). Qed.
Lemma lem194765 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem194766 (m : nat) (p : nat) (n : nat) : (term285 m p n) = (term285 m p n).
Proof. exact (MK_COMB (@lem194765) (@lem194764 m p n)). Qed.
Lemma lem194767 (m : nat) (p : nat) (n : nat) : (term287 m p n) = (term287 m p n).
Proof. exact (MK_COMB (@lem194766 m p n) (@lem194754)). Qed.
Lemma lem194770 (m : nat) (p : nat) (n : nat) : (term288 m p n) = (term288 m p n).
Proof. exact (eq_refl (term288 m p n)). Qed.
Lemma lem194771 (m : nat) (p : nat) (n : nat) : (term290 m p n) = (term290 m p n).
Proof. exact (MK_COMB (@lem194770 m p n) (@lem194767 m p n)). Qed.
Lemma lem194776 (p : nat) : (term291 p) = (term291 p).
Proof. exact (eq_refl (term291 p)). Qed.
Lemma lem194777 (m : nat) (p : nat) (n : nat) : (term292 m p n) = (term292 m p n).
Proof. exact (MK_COMB (@lem194776 p) (@lem194771 m p n)). Qed.
Lemma lem194778 (p : nat) (n : nat) : (term294 p n) = (term294 p n).
Proof. exact (fun_ext (fun m : nat => @lem194777 m p n)). Qed.
Lemma lem194779 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194780 (p : nat) (n : nat) : (term296 p n) = (term296 p n).
Proof. exact (MK_COMB (@lem194779) (@lem194778 p n)). Qed.
Lemma lem194781 (n : nat) : (term298 n) = (term298 n).
Proof. exact (fun_ext (fun p : nat => @lem194780 p n)). Qed.
Lemma lem194782 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194783 (n : nat) : (term300 n) = (term300 n).
Proof. exact (MK_COMB (@lem194782) (@lem194781 n)). Qed.
Lemma lem194784 : term302 = term302.
Proof. exact (fun_ext (fun n : nat => @lem194783 n)). Qed.
Lemma lem194785 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem194786 : term304 = term304.
Proof. exact (MK_COMB (@lem194785) (@lem194784)). Qed.
Lemma lem194895 : term303 = term304.
Proof. exact (TRANS (@lem194693) (@lem194786)). Qed.
Lemma lem194896 : term304 = term303.
Proof. exact (SYM (@lem194895)). Qed.
Lemma lem194899 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) : term269 m p n.
Proof. exact (h1). Qed.
Lemma lem194901 (h1 : term320) : term320.
Proof. exact (h1). Qed.
Lemma lem194902 (h1 : term311) : term311.
Proof. exact (h1). Qed.
Lemma lem194903 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem194915 (m : nat) (p : nat) (n : nat) (h1 : term214 m p n) : term214 m p n.
Proof. exact (h1). Qed.
Lemma lem194922 (m : nat) (k : nat) (p : nat) (n : nat) : (term325 m k p n) = (term326 m k p n).
Proof. exact (@lem17362 (term237 p k m) (term259 k p n)). Qed.
Lemma lem194923 (P : nat -> Prop) : (term327 P) = (term328 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem194924 (m : nat) (p : nat) (n : nat) : (term269 m p n) = (term329 m p n).
Proof. exact (@lem194923 (term265 m p n)). Qed.
Lemma lem194925 (m : nat) (k : nat) (p : nat) (n : nat) : (term330 m p n k) = (term263 m k p n).
Proof. exact (eq_refl (term330 m p n k)). Qed.
Lemma lem194926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem194927 (m : nat) (k : nat) (p : nat) (n : nat) : (term331 m p n k) = (term325 m k p n).
Proof. exact (MK_COMB (@lem194926) (@lem194925 m k p n)). Qed.
Lemma lem194928 (m : nat) (k : nat) (p : nat) (n : nat) : (term331 m p n k) = (term326 m k p n).
Proof. exact (TRANS (@lem194927 m k p n) (@lem194922 m k p n)). Qed.
Lemma lem194929 (m : nat) (p : nat) (n : nat) : (term332 m p n) = (term333 m p n).
Proof. exact (fun_ext (fun k : nat => @lem194928 m k p n)). Qed.
Lemma lem194930 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem194931 (m : nat) (p : nat) (n : nat) : (term329 m p n) = (term334 m p n).
Proof. exact (MK_COMB (@lem194930) (@lem194929 m p n)). Qed.
Lemma lem194984 (m : nat) (p : nat) (n : nat) : (term269 m p n) = (term334 m p n).
Proof. exact (TRANS (@lem194924 m p n) (@lem194931 m p n)). Qed.
Lemma lem194985 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) : term334 m p n.
Proof. exact (EQ_MP (@lem194984 m p n) (@lem194899 m p n h1)). Qed.
Lemma lem195012 (m : nat) (p : nat) (n : nat) (q : nat) : (term335 m p n q) = (term336 m p n q).
Proof. exact (@lem17045 (Peano.le m p) (Peano.le n q)). Qed.
Lemma lem195013 (m : nat) (n : nat) (p : nat) (q : nat) : (term337 m n p q) = (term337 m n p q).
Proof. exact (eq_refl (term337 m n p q)). Qed.
Lemma lem195014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem195015 (m : nat) (p : nat) (n : nat) (q : nat) : (term338 m p n q) = (term339 m p n q).
Proof. exact (MK_COMB (@lem195014) (@lem195012 m p n q)). Qed.
Lemma lem195016 (m : nat) (n : nat) (p : nat) (q : nat) : (term340 m n p q) = (term341 m n p q).
Proof. exact (MK_COMB (@lem195015 m p n q) (@lem195013 m n p q)). Qed.
Lemma lem195017 (m : nat) (n : nat) (p : nat) (q : nat) : (term312 m n p q) = (term340 m n p q).
Proof. exact (@lem17265 (term342 m p n q) (term337 m n p q)). Qed.
Lemma lem195018 (m : nat) (n : nat) (p : nat) (q : nat) : (term312 m n p q) = (term341 m n p q).
Proof. exact (TRANS (@lem195017 m n p q) (@lem195016 m n p q)). Qed.
Lemma lem195019 (m : nat) (n : nat) (p : nat) : (term313 m n p) = (term343 m n p).
Proof. exact (fun_ext (fun q : nat => @lem195018 m n p q)). Qed.
Lemma lem195020 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195021 (m : nat) (n : nat) (p : nat) : (term314 m n p) = (term344 m n p).
Proof. exact (MK_COMB (@lem195020) (@lem195019 m n p)). Qed.
Lemma lem195022 (m : nat) (n : nat) : (term315 m n) = (term345 m n).
Proof. exact (fun_ext (fun p : nat => @lem195021 m n p)). Qed.
Lemma lem195023 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195024 (m : nat) (n : nat) : (term316 m n) = (term346 m n).
Proof. exact (MK_COMB (@lem195023) (@lem195022 m n)). Qed.
Lemma lem195025 (m : nat) : (term317 m) = (term347 m).
Proof. exact (fun_ext (fun n : nat => @lem195024 m n)). Qed.
Lemma lem195026 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195027 (m : nat) : (term318 m) = (term348 m).
Proof. exact (MK_COMB (@lem195026) (@lem195025 m)). Qed.
Lemma lem195028 : term319 = term349.
Proof. exact (fun_ext (fun m : nat => @lem195027 m)). Qed.
Lemma lem195029 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195094 : term320 = term350.
Proof. exact (MK_COMB (@lem195029) (@lem195028)). Qed.
Lemma lem195095 (h1 : term320) : term350.
Proof. exact (EQ_MP (@lem195094) (@lem194901 h1)). Qed.
Lemma lem195102 (m : nat) (n : nat) (p : nat) : (term351 m n p) = (term352 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem195103 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem195104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem195105 (m : nat) (n : nat) (p : nat) : (term353 m n p) = (term354 m n p).
Proof. exact (MK_COMB (@lem195104) (@lem195102 m n p)). Qed.
Lemma lem195106 (n : nat) (m : nat) (p : nat) : (term355 n m p) = (term356 n m p).
Proof. exact (MK_COMB (@lem195105 m n p) (@lem195103 m p)). Qed.
Lemma lem195107 (n : nat) (m : nat) (p : nat) : (term305 n m p) = (term355 n m p).
Proof. exact (@lem17265 (term357 m n p) (Peano.le m p)). Qed.
Lemma lem195108 (n : nat) (m : nat) (p : nat) : (term305 n m p) = (term356 n m p).
Proof. exact (TRANS (@lem195107 n m p) (@lem195106 n m p)). Qed.
Lemma lem195109 (n : nat) (m : nat) : (term306 n m) = (term358 n m).
Proof. exact (fun_ext (fun p : nat => @lem195108 n m p)). Qed.
Lemma lem195110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195111 (n : nat) (m : nat) : (term307 n m) = (term359 n m).
Proof. exact (MK_COMB (@lem195110) (@lem195109 n m)). Qed.
Lemma lem195112 (m : nat) : (term308 m) = (term360 m).
Proof. exact (fun_ext (fun n : nat => @lem195111 n m)). Qed.
Lemma lem195113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195114 (m : nat) : (term309 m) = (term361 m).
Proof. exact (MK_COMB (@lem195113) (@lem195112 m)). Qed.
Lemma lem195115 : term310 = term362.
Proof. exact (fun_ext (fun m : nat => @lem195114 m)). Qed.
Lemma lem195116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195177 : term311 = term363.
Proof. exact (MK_COMB (@lem195116) (@lem195115)). Qed.
Lemma lem195178 (h1 : term311) : term363.
Proof. exact (EQ_MP (@lem195177) (@lem194902 h1)). Qed.
Lemma lem195179 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem195180 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem195179 n)). Qed.
Lemma lem195181 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195190 : term42 = term42.
Proof. exact (MK_COMB (@lem195181) (@lem195180)). Qed.
Lemma lem195191 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem195190) (@lem194903 h1)). Qed.
Lemma lem195212 (m : nat) (p : nat) (n : nat) (h1 : term214 m p n) : term214 m p n.
Proof. exact (h1). Qed.
Lemma lem195265 (m : nat) (n : nat) (p : nat) (q : nat) : (term341 m n p q) = (term341 m n p q).
Proof. exact (eq_refl (term341 m n p q)). Qed.
Lemma lem195266 (m : nat) (n : nat) (p : nat) : (term343 m n p) = (term343 m n p).
Proof. exact (fun_ext (fun q : nat => @lem195265 m n p q)). Qed.
Lemma lem195267 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195268 (m : nat) (n : nat) (p : nat) : (term344 m n p) = (term344 m n p).
Proof. exact (MK_COMB (@lem195267) (@lem195266 m n p)). Qed.
Lemma lem195269 (m : nat) (n : nat) : (term345 m n) = (term345 m n).
Proof. exact (fun_ext (fun p : nat => @lem195268 m n p)). Qed.
Lemma lem195270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195271 (m : nat) (n : nat) : (term346 m n) = (term346 m n).
Proof. exact (MK_COMB (@lem195270) (@lem195269 m n)). Qed.
Lemma lem195272 (m : nat) : (term347 m) = (term347 m).
Proof. exact (fun_ext (fun n : nat => @lem195271 m n)). Qed.
Lemma lem195273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195274 (m : nat) : (term348 m) = (term348 m).
Proof. exact (MK_COMB (@lem195273) (@lem195272 m)). Qed.
Lemma lem195275 : term349 = term349.
Proof. exact (fun_ext (fun m : nat => @lem195274 m)). Qed.
Lemma lem195276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195277 : term350 = term350.
Proof. exact (MK_COMB (@lem195276) (@lem195275)). Qed.
Lemma lem195278 (h1 : term320) : term350.
Proof. exact (EQ_MP (@lem195277) (@lem195095 h1)). Qed.
Lemma lem195303 (n : nat) (m : nat) (p : nat) : (term356 n m p) = (term356 n m p).
Proof. exact (eq_refl (term356 n m p)). Qed.
Lemma lem195304 (n : nat) (m : nat) : (term358 n m) = (term358 n m).
Proof. exact (fun_ext (fun p : nat => @lem195303 n m p)). Qed.
Lemma lem195305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195306 (n : nat) (m : nat) : (term359 n m) = (term359 n m).
Proof. exact (MK_COMB (@lem195305) (@lem195304 n m)). Qed.
Lemma lem195307 (m : nat) : (term360 m) = (term360 m).
Proof. exact (fun_ext (fun n : nat => @lem195306 n m)). Qed.
Lemma lem195308 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195309 (m : nat) : (term361 m) = (term361 m).
Proof. exact (MK_COMB (@lem195308) (@lem195307 m)). Qed.
Lemma lem195310 : term362 = term362.
Proof. exact (fun_ext (fun m : nat => @lem195309 m)). Qed.
Lemma lem195311 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195312 : term363 = term363.
Proof. exact (MK_COMB (@lem195311) (@lem195310)). Qed.
Lemma lem195313 (h1 : term311) : term363.
Proof. exact (EQ_MP (@lem195312) (@lem195178 h1)). Qed.
Lemma lem195318 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem195319 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem195318 n)). Qed.
Lemma lem195320 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195321 : term42 = term42.
Proof. exact (MK_COMB (@lem195320) (@lem195319)). Qed.
Lemma lem195322 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem195321) (@lem195191 h1)). Qed.
Lemma lem195350 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term326 m k p n) : term326 m k p n.
Proof. exact (h1). Qed.
Lemma lem195360 (m : nat) (p : nat) (n : nat) (h1 : term214 m p n) : term214 m p n.
Proof. exact (h1). Qed.
Lemma lem195384 (m : nat) (n : nat) (p : nat) (q : nat) : (term341 m n p q) = (term341 m n p q).
Proof. exact (eq_refl (term341 m n p q)). Qed.
Lemma lem195385 (m : nat) (n : nat) (p : nat) : (term343 m n p) = (term343 m n p).
Proof. exact (fun_ext (fun q : nat => @lem195384 m n p q)). Qed.
Lemma lem195386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195387 (m : nat) (n : nat) (p : nat) : (term344 m n p) = (term344 m n p).
Proof. exact (MK_COMB (@lem195386) (@lem195385 m n p)). Qed.
Lemma lem195388 (m : nat) (n : nat) : (term345 m n) = (term345 m n).
Proof. exact (fun_ext (fun p : nat => @lem195387 m n p)). Qed.
Lemma lem195389 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195390 (m : nat) (n : nat) : (term346 m n) = (term346 m n).
Proof. exact (MK_COMB (@lem195389) (@lem195388 m n)). Qed.
Lemma lem195391 (m : nat) : (term347 m) = (term347 m).
Proof. exact (fun_ext (fun n : nat => @lem195390 m n)). Qed.
Lemma lem195392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195393 (m : nat) : (term348 m) = (term348 m).
Proof. exact (MK_COMB (@lem195392) (@lem195391 m)). Qed.
Lemma lem195394 : term349 = term349.
Proof. exact (fun_ext (fun m : nat => @lem195393 m)). Qed.
Lemma lem195395 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195397 : term350 = term350.
Proof. exact (MK_COMB (@lem195395) (@lem195394)). Qed.
Lemma lem195398 (h1 : term320) : term350.
Proof. exact (EQ_MP (@lem195397) (@lem195278 h1)). Qed.
Lemma lem195412 (n : nat) (m : nat) (p : nat) : (term356 n m p) = (term356 n m p).
Proof. exact (eq_refl (term356 n m p)). Qed.
Lemma lem195413 (n : nat) (m : nat) : (term358 n m) = (term358 n m).
Proof. exact (fun_ext (fun p : nat => @lem195412 n m p)). Qed.
Lemma lem195414 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195415 (n : nat) (m : nat) : (term359 n m) = (term359 n m).
Proof. exact (MK_COMB (@lem195414) (@lem195413 n m)). Qed.
Lemma lem195416 (m : nat) : (term360 m) = (term360 m).
Proof. exact (fun_ext (fun n : nat => @lem195415 n m)). Qed.
Lemma lem195417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195418 (m : nat) : (term361 m) = (term361 m).
Proof. exact (MK_COMB (@lem195417) (@lem195416 m)). Qed.
Lemma lem195419 : term362 = term362.
Proof. exact (fun_ext (fun m : nat => @lem195418 m)). Qed.
Lemma lem195420 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195422 : term363 = term363.
Proof. exact (MK_COMB (@lem195420) (@lem195419)). Qed.
Lemma lem195423 (h1 : term311) : term363.
Proof. exact (EQ_MP (@lem195422) (@lem195313 h1)). Qed.
Lemma lem195425 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem195426 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem195425 n)). Qed.
Lemma lem195427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem195429 : term42 = term42.
Proof. exact (MK_COMB (@lem195427) (@lem195426)). Qed.
Lemma lem195430 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem195429) (@lem195322 h1)). Qed.
Lemma lem195445 (_3926 : nat) (h1 : term320) : term364 _3926.
Proof. exact (@lem195398 h1 _3926). Qed.
Lemma lem195446 (_3926 : nat) : (term364 _3926) = (term348 _3926).
Proof. exact (eq_refl (term364 _3926)). Qed.
Lemma lem195447 (_3926 : nat) (h1 : term320) : term348 _3926.
Proof. exact (EQ_MP (@lem195446 _3926) (@lem195445 _3926 h1)). Qed.
Lemma lem195448 (_3926 : nat) (_3927 : nat) (h1 : term320) : term365 _3926 _3927.
Proof. exact (@lem195447 _3926 h1 _3927). Qed.
Lemma lem195449 (_3926 : nat) (_3927 : nat) : (term365 _3926 _3927) = (term346 _3926 _3927).
Proof. exact (eq_refl (term365 _3926 _3927)). Qed.
Lemma lem195450 (_3926 : nat) (_3927 : nat) (h1 : term320) : term346 _3926 _3927.
Proof. exact (EQ_MP (@lem195449 _3926 _3927) (@lem195448 _3926 _3927 h1)). Qed.
Lemma lem195451 (_3926 : nat) (_3927 : nat) (_3928 : nat) (h1 : term320) : term366 _3926 _3927 _3928.
Proof. exact (@lem195450 _3926 _3927 h1 _3928). Qed.
Lemma lem195452 (_3926 : nat) (_3927 : nat) (_3928 : nat) : (term366 _3926 _3927 _3928) = (term344 _3926 _3927 _3928).
Proof. exact (eq_refl (term366 _3926 _3927 _3928)). Qed.
Lemma lem195453 (_3926 : nat) (_3927 : nat) (_3928 : nat) (h1 : term320) : term344 _3926 _3927 _3928.
Proof. exact (EQ_MP (@lem195452 _3926 _3927 _3928) (@lem195451 _3926 _3927 _3928 h1)). Qed.
Lemma lem195454 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) (h1 : term320) : term367 _3926 _3927 _3928 _3929.
Proof. exact (@lem195453 _3926 _3927 _3928 h1 _3929). Qed.
Lemma lem195455 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) : (term367 _3926 _3927 _3928 _3929) = (term341 _3926 _3927 _3928 _3929).
Proof. exact (eq_refl (term367 _3926 _3927 _3928 _3929)). Qed.
Lemma lem195456 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) (h1 : term320) : term341 _3926 _3927 _3928 _3929.
Proof. exact (EQ_MP (@lem195455 _3926 _3927 _3928 _3929) (@lem195454 _3926 _3927 _3928 _3929 h1)). Qed.
Lemma lem195457 (_3930 : nat) (h1 : term311) : term368 _3930.
Proof. exact (@lem195423 h1 _3930). Qed.
Lemma lem195458 (_3930 : nat) : (term368 _3930) = (term361 _3930).
Proof. exact (eq_refl (term368 _3930)). Qed.
Lemma lem195459 (_3930 : nat) (h1 : term311) : term361 _3930.
Proof. exact (EQ_MP (@lem195458 _3930) (@lem195457 _3930 h1)). Qed.
Lemma lem195460 (_3930 : nat) (_3931 : nat) (h1 : term311) : term369 _3930 _3931.
Proof. exact (@lem195459 _3930 h1 _3931). Qed.
Lemma lem195461 (_3931 : nat) (_3930 : nat) : (term369 _3930 _3931) = (term359 _3931 _3930).
Proof. exact (eq_refl (term369 _3930 _3931)). Qed.
Lemma lem195462 (_3931 : nat) (_3930 : nat) (h1 : term311) : term359 _3931 _3930.
Proof. exact (EQ_MP (@lem195461 _3931 _3930) (@lem195460 _3930 _3931 h1)). Qed.
Lemma lem195463 (_3931 : nat) (_3930 : nat) (_3932 : nat) (h1 : term311) : term370 _3931 _3930 _3932.
Proof. exact (@lem195462 _3931 _3930 h1 _3932). Qed.
Lemma lem195464 (_3931 : nat) (_3930 : nat) (_3932 : nat) : (term370 _3931 _3930 _3932) = (term356 _3931 _3930 _3932).
Proof. exact (eq_refl (term370 _3931 _3930 _3932)). Qed.
Lemma lem195465 (_3931 : nat) (_3930 : nat) (_3932 : nat) (h1 : term311) : term356 _3931 _3930 _3932.
Proof. exact (EQ_MP (@lem195464 _3931 _3930 _3932) (@lem195463 _3931 _3930 _3932 h1)). Qed.
Lemma lem195466 (_3933 : nat) (h1 : term42) : term110 _3933.
Proof. exact (@lem195430 h1 _3933). Qed.
Lemma lem195467 (_3933 : nat) : (term110 _3933) = (Peano.le _3933 _3933).
Proof. exact (eq_refl (term110 _3933)). Qed.
Lemma lem195472 (m : nat) (p : nat) (n : nat) (h1 : term214 m p n) : term214 m p n.
Proof. exact (h1). Qed.
Lemma lem195485 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) : (term341 _3926 _3927 _3928 _3929) = (term371 _3926 _3927 _3928 _3929).
Proof. exact (@lem192854 (term159 _3926 _3928) (term159 _3927 _3929) (term337 _3926 _3927 _3928 _3929)). Qed.
Lemma lem195486 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) (h1 : term320) : term371 _3926 _3927 _3928 _3929.
Proof. exact (EQ_MP (@lem195485 _3926 _3927 _3928 _3929) (@lem195456 _3926 _3927 _3928 _3929 h1)). Qed.
Lemma lem195497 (_3931 : nat) (_3930 : nat) (_3932 : nat) : (term356 _3931 _3930 _3932) = (term372 _3931 _3930 _3932).
Proof. exact (@lem192854 (term159 _3930 _3931) (term159 _3931 _3932) (Peano.le _3930 _3932)). Qed.
Lemma lem195498 (_3931 : nat) (_3930 : nat) (_3932 : nat) (h1 : term311) : term372 _3931 _3930 _3932.
Proof. exact (EQ_MP (@lem195497 _3931 _3930 _3932) (@lem195465 _3931 _3930 _3932 h1)). Qed.
Lemma lem195504 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term326 m k p n) : term373 k p n.
Proof. exact (proj2 (@lem195350 m k p n h1)). Qed.
Lemma lem195565 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term326 m k p n) : term237 p k m.
Proof. exact (proj1 (@lem195350 m k p n h1)). Qed.
Lemma lem195566 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term326 m k p n) : term374 p k m.
Proof. exact (fun h0 : term375 p k m => @lem195565 m k p n h1). Qed.
Lemma lem195568 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem195569 (p : nat) (k : nat) (m : nat) : (term374 p k m) = (term237 p k m).
Proof. exact (@lem195568 (term237 p k m)). Qed.
Lemma lem195570 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term326 m k p n) : term237 p k m.
Proof. exact (EQ_MP (@lem195569 p k m) (@lem195566 m k p n h1)). Qed.
Lemma lem195572 (_3933 : nat) (h1 : term42) : Peano.le _3933 _3933.
Proof. exact (EQ_MP (@lem195467 _3933) (@lem195466 _3933 h1)). Qed.
Lemma lem195573 (p : nat) (h1 : term42) : Peano.le p p.
Proof. exact (@lem195572 p h1). Qed.
Lemma lem195574 (p : nat) (h1 : term42) : term156 p.
Proof. exact (fun h0 : term157 p => @lem195573 p h1). Qed.
Lemma lem195576 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem195577 (p : nat) : (term156 p) = (Peano.le p p).
Proof. exact (@lem195576 (Peano.le p p)). Qed.
Lemma lem195578 (p : nat) (h1 : term42) : Peano.le p p.
Proof. exact (EQ_MP (@lem195577 p) (@lem195574 p h1)). Qed.
Lemma lem195594 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem195595 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term376 _3926 _3927 _3928 _3929) = (term377 _3926 _3928 _3927 _3929).
Proof. exact (@lem195594 (term337 _3926 _3927 _3928 _3929) (term159 _3927 _3929)). Qed.
Lemma lem195601 (_3926 : nat) (_3928 : nat) : (term378 _3926 _3928) = (term378 _3926 _3928).
Proof. exact (eq_refl (term378 _3926 _3928)). Qed.
Lemma lem195602 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term371 _3926 _3927 _3928 _3929) = (term379 _3926 _3928 _3927 _3929).
Proof. exact (MK_COMB (@lem195601 _3926 _3928) (@lem195595 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195606 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem195607 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term379 _3926 _3928 _3927 _3929) = (term380 _3926 _3928 _3927 _3929).
Proof. exact (@lem195606 (term337 _3926 _3927 _3928 _3929) (term159 _3926 _3928) (term159 _3927 _3929)). Qed.
Lemma lem195623 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term371 _3926 _3927 _3928 _3929) = (term380 _3926 _3928 _3927 _3929).
Proof. exact (TRANS (@lem195602 _3926 _3928 _3927 _3929) (@lem195607 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem195625 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term381 _3926 _3927 _3928 _3929) = (term382 _3926 _3928 _3927 _3929).
Proof. exact (MK_COMB (@lem195624) (@lem195623 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195641 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term380 _3926 _3928 _3927 _3929) = (term380 _3926 _3928 _3927 _3929).
Proof. exact (eq_refl (term380 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195642 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : ((term371 _3926 _3927 _3928 _3929) = (term380 _3926 _3928 _3927 _3929)) = ((term380 _3926 _3928 _3927 _3929) = (term380 _3926 _3928 _3927 _3929)).
Proof. exact (MK_COMB (@lem195625 _3926 _3928 _3927 _3929) (@lem195641 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195644 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem195645 (x : Prop) : (x = x) = True.
Proof. exact (@lem195644 Prop x). Qed.
Lemma lem195646 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : ((term380 _3926 _3928 _3927 _3929) = (term380 _3926 _3928 _3927 _3929)) = True.
Proof. exact (@lem195645 (term380 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195647 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : ((term371 _3926 _3927 _3928 _3929) = (term380 _3926 _3928 _3927 _3929)) = True.
Proof. exact (TRANS (@lem195642 _3926 _3928 _3927 _3929) (@lem195646 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195648 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : True = ((term371 _3926 _3927 _3928 _3929) = (term380 _3926 _3928 _3927 _3929)).
Proof. exact (SYM (@lem195647 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195649 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term371 _3926 _3927 _3928 _3929) = (term380 _3926 _3928 _3927 _3929).
Proof. exact (EQ_MP (@lem195648 _3926 _3928 _3927 _3929) (@lem0)). Qed.
Lemma lem195650 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) (h1 : term320) : term380 _3926 _3928 _3927 _3929.
Proof. exact (EQ_MP (@lem195649 _3926 _3928 _3927 _3929) (@lem195486 _3926 _3927 _3928 _3929 h1)). Qed.
Lemma lem195652 (b : Prop) (a : Prop) : (a \/ b) = (term135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem195653 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) : (term380 _3926 _3928 _3927 _3929) = (term383 _3926 _3927 _3928 _3929).
Proof. exact (@lem195652 (term336 _3926 _3928 _3927 _3929) (term337 _3926 _3927 _3928 _3929)). Qed.
Lemma lem195655 (a : Prop) (b : Prop) : (term138 a b) = (term139 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem195656 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term384 _3926 _3928 _3927 _3929) = (term385 _3926 _3928 _3927 _3929).
Proof. exact (@lem195655 (term159 _3926 _3928) (term159 _3927 _3929)). Qed.
Lemma lem195658 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem195659 (_3926 : nat) (_3928 : nat) : (term163 _3926 _3928) = (Peano.le _3926 _3928).
Proof. exact (@lem195658 (Peano.le _3926 _3928)). Qed.
Lemma lem195660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem195661 (_3926 : nat) (_3928 : nat) : (term386 _3926 _3928) = (term387 _3926 _3928).
Proof. exact (MK_COMB (@lem195660) (@lem195659 _3926 _3928)). Qed.
Lemma lem195663 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem195664 (_3927 : nat) (_3929 : nat) : (term163 _3927 _3929) = (Peano.le _3927 _3929).
Proof. exact (@lem195663 (Peano.le _3927 _3929)). Qed.
Lemma lem195665 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term385 _3926 _3928 _3927 _3929) = (term342 _3926 _3928 _3927 _3929).
Proof. exact (MK_COMB (@lem195661 _3926 _3928) (@lem195664 _3927 _3929)). Qed.
Lemma lem195666 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term384 _3926 _3928 _3927 _3929) = (term342 _3926 _3928 _3927 _3929).
Proof. exact (TRANS (@lem195656 _3926 _3928 _3927 _3929) (@lem195665 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem195668 (_3926 : nat) (_3928 : nat) (_3927 : nat) (_3929 : nat) : (term388 _3926 _3928 _3927 _3929) = (term389 _3926 _3928 _3927 _3929).
Proof. exact (MK_COMB (@lem195667) (@lem195666 _3926 _3928 _3927 _3929)). Qed.
Lemma lem195669 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) : (term337 _3926 _3927 _3928 _3929) = (term337 _3926 _3927 _3928 _3929).
Proof. exact (eq_refl (term337 _3926 _3927 _3928 _3929)). Qed.
Lemma lem195670 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) : (term383 _3926 _3927 _3928 _3929) = (term312 _3926 _3927 _3928 _3929).
Proof. exact (MK_COMB (@lem195668 _3926 _3928 _3927 _3929) (@lem195669 _3926 _3927 _3928 _3929)). Qed.
Lemma lem195671 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) : (term380 _3926 _3928 _3927 _3929) = (term312 _3926 _3927 _3928 _3929).
Proof. exact (TRANS (@lem195653 _3926 _3927 _3928 _3929) (@lem195670 _3926 _3927 _3928 _3929)). Qed.
Lemma lem195673 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term42) (h2 : term326 m k p n) : term390 k m p.
Proof. exact (conj (@lem195570 m k p n h2) (@lem195578 p h1)). Qed.
Lemma lem195675 (_3926 : nat) (_3927 : nat) (_3928 : nat) (_3929 : nat) (h1 : term320) : term312 _3926 _3927 _3928 _3929.
Proof. exact (EQ_MP (@lem195671 _3926 _3927 _3928 _3929) (@lem195650 _3926 _3928 _3927 _3929 h1)). Qed.
Lemma lem195676 (k : nat) (m : nat) (p : nat) (h1 : term320) : term391 k m p.
Proof. exact (@lem195675 (Nat.mul p k) p m p h1). Qed.
Lemma lem195679 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term42) (h3 : term326 m k p n) : term392 k m p.
Proof. exact (@lem195676 k m p h1 (@lem195673 m k p n h2 h3)). Qed.
Lemma lem195680 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term42) (h3 : term326 m k p n) : term393 k m p.
Proof. exact (fun h0 : term394 k m p => @lem195679 m k p n h1 h2 h3). Qed.
Lemma lem195682 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem195683 (k : nat) (m : nat) (p : nat) : (term393 k m p) = (term392 k m p).
Proof. exact (@lem195682 (term392 k m p)). Qed.
Lemma lem195684 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term42) (h3 : term326 m k p n) : term392 k m p.
Proof. exact (EQ_MP (@lem195683 k m p) (@lem195680 m k p n h1 h2 h3)). Qed.
Lemma lem195686 (m : nat) (p : nat) (n : nat) (h1 : term214 m p n) : term214 m p n.
Proof. exact (h1). Qed.
Lemma lem195687 (m : nat) (p : nat) (n : nat) (h1 : term214 m p n) : term395 m p n.
Proof. exact (fun h0 : term396 m p n => @lem195686 m p n h1). Qed.
Lemma lem195689 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem195690 (m : nat) (p : nat) (n : nat) : (term395 m p n) = (term214 m p n).
Proof. exact (@lem195689 (term214 m p n)). Qed.
Lemma lem195691 (m : nat) (p : nat) (n : nat) (h1 : term214 m p n) : term214 m p n.
Proof. exact (EQ_MP (@lem195690 m p n) (@lem195687 m p n h1)). Qed.
Lemma lem195707 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem195708 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term397 _3931 _3930 _3932) = (term398 _3930 _3931 _3932).
Proof. exact (@lem195707 (Peano.le _3930 _3932) (term159 _3931 _3932)). Qed.
Lemma lem195714 (_3930 : nat) (_3931 : nat) : (term378 _3930 _3931) = (term378 _3930 _3931).
Proof. exact (eq_refl (term378 _3930 _3931)). Qed.
Lemma lem195715 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term372 _3931 _3930 _3932) = (term399 _3930 _3931 _3932).
Proof. exact (MK_COMB (@lem195714 _3930 _3931) (@lem195708 _3930 _3931 _3932)). Qed.
Lemma lem195719 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem195720 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term399 _3930 _3931 _3932) = (term400 _3930 _3931 _3932).
Proof. exact (@lem195719 (Peano.le _3930 _3932) (term159 _3930 _3931) (term159 _3931 _3932)). Qed.
Lemma lem195736 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term372 _3931 _3930 _3932) = (term400 _3930 _3931 _3932).
Proof. exact (TRANS (@lem195715 _3930 _3931 _3932) (@lem195720 _3930 _3931 _3932)). Qed.
Lemma lem195737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem195738 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term401 _3931 _3930 _3932) = (term402 _3930 _3931 _3932).
Proof. exact (MK_COMB (@lem195737) (@lem195736 _3930 _3931 _3932)). Qed.
Lemma lem195754 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term400 _3930 _3931 _3932) = (term400 _3930 _3931 _3932).
Proof. exact (eq_refl (term400 _3930 _3931 _3932)). Qed.
Lemma lem195755 (_3930 : nat) (_3931 : nat) (_3932 : nat) : ((term372 _3931 _3930 _3932) = (term400 _3930 _3931 _3932)) = ((term400 _3930 _3931 _3932) = (term400 _3930 _3931 _3932)).
Proof. exact (MK_COMB (@lem195738 _3930 _3931 _3932) (@lem195754 _3930 _3931 _3932)). Qed.
Lemma lem195757 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem195758 (x : Prop) : (x = x) = True.
Proof. exact (@lem195757 Prop x). Qed.
Lemma lem195759 (_3930 : nat) (_3931 : nat) (_3932 : nat) : ((term400 _3930 _3931 _3932) = (term400 _3930 _3931 _3932)) = True.
Proof. exact (@lem195758 (term400 _3930 _3931 _3932)). Qed.
Lemma lem195760 (_3930 : nat) (_3931 : nat) (_3932 : nat) : ((term372 _3931 _3930 _3932) = (term400 _3930 _3931 _3932)) = True.
Proof. exact (TRANS (@lem195755 _3930 _3931 _3932) (@lem195759 _3930 _3931 _3932)). Qed.
Lemma lem195761 (_3930 : nat) (_3931 : nat) (_3932 : nat) : True = ((term372 _3931 _3930 _3932) = (term400 _3930 _3931 _3932)).
Proof. exact (SYM (@lem195760 _3930 _3931 _3932)). Qed.
Lemma lem195762 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term372 _3931 _3930 _3932) = (term400 _3930 _3931 _3932).
Proof. exact (EQ_MP (@lem195761 _3930 _3931 _3932) (@lem0)). Qed.
Lemma lem195763 (_3930 : nat) (_3931 : nat) (_3932 : nat) (h1 : term311) : term400 _3930 _3931 _3932.
Proof. exact (EQ_MP (@lem195762 _3930 _3931 _3932) (@lem195498 _3931 _3930 _3932 h1)). Qed.
Lemma lem195765 (b : Prop) (a : Prop) : (a \/ b) = (term135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem195766 (_3931 : nat) (_3930 : nat) (_3932 : nat) : (term400 _3930 _3931 _3932) = (term403 _3931 _3930 _3932).
Proof. exact (@lem195765 (term352 _3930 _3931 _3932) (Peano.le _3930 _3932)). Qed.
Lemma lem195768 (a : Prop) (b : Prop) : (term138 a b) = (term139 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem195769 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term404 _3930 _3931 _3932) = (term405 _3930 _3931 _3932).
Proof. exact (@lem195768 (term159 _3930 _3931) (term159 _3931 _3932)). Qed.
Lemma lem195771 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem195772 (_3930 : nat) (_3931 : nat) : (term163 _3930 _3931) = (Peano.le _3930 _3931).
Proof. exact (@lem195771 (Peano.le _3930 _3931)). Qed.
Lemma lem195773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem195774 (_3930 : nat) (_3931 : nat) : (term386 _3930 _3931) = (term387 _3930 _3931).
Proof. exact (MK_COMB (@lem195773) (@lem195772 _3930 _3931)). Qed.
Lemma lem195776 (a : Prop) : (term142 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem195777 (_3931 : nat) (_3932 : nat) : (term163 _3931 _3932) = (Peano.le _3931 _3932).
Proof. exact (@lem195776 (Peano.le _3931 _3932)). Qed.
Lemma lem195778 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term405 _3930 _3931 _3932) = (term357 _3930 _3931 _3932).
Proof. exact (MK_COMB (@lem195774 _3930 _3931) (@lem195777 _3931 _3932)). Qed.
Lemma lem195779 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term404 _3930 _3931 _3932) = (term357 _3930 _3931 _3932).
Proof. exact (TRANS (@lem195769 _3930 _3931 _3932) (@lem195778 _3930 _3931 _3932)). Qed.
Lemma lem195780 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem195781 (_3930 : nat) (_3931 : nat) (_3932 : nat) : (term406 _3930 _3931 _3932) = (term407 _3930 _3931 _3932).
Proof. exact (MK_COMB (@lem195780) (@lem195779 _3930 _3931 _3932)). Qed.
Lemma lem195782 (_3930 : nat) (_3932 : nat) : (Peano.le _3930 _3932) = (Peano.le _3930 _3932).
Proof. exact (eq_refl (Peano.le _3930 _3932)). Qed.
Lemma lem195783 (_3931 : nat) (_3930 : nat) (_3932 : nat) : (term403 _3931 _3930 _3932) = (term305 _3931 _3930 _3932).
Proof. exact (MK_COMB (@lem195781 _3930 _3931 _3932) (@lem195782 _3930 _3932)). Qed.
Lemma lem195784 (_3931 : nat) (_3930 : nat) (_3932 : nat) : (term400 _3930 _3931 _3932) = (term305 _3931 _3930 _3932).
Proof. exact (TRANS (@lem195766 _3931 _3930 _3932) (@lem195783 _3931 _3930 _3932)). Qed.
Lemma lem195786 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term42) (h3 : term326 m k p n) (h4 : term214 m p n) : term408 k m p n.
Proof. exact (conj (@lem195684 m k p n h1 h2 h3) (@lem195691 m p n h4)). Qed.
Lemma lem195788 (_3931 : nat) (_3930 : nat) (_3932 : nat) (h1 : term311) : term305 _3931 _3930 _3932.
Proof. exact (EQ_MP (@lem195784 _3931 _3930 _3932) (@lem195763 _3930 _3931 _3932 h1)). Qed.
Lemma lem195789 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term311) : term409 m k p n.
Proof. exact (@lem195788 (Nat.add m p) (term256 k p) n h1). Qed.
Lemma lem195792 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : term259 k p n.
Proof. exact (@lem195789 m k p n h2 (@lem195786 k m p n h1 h3 h4 h5)). Qed.
Lemma lem195793 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : term410 k p n.
Proof. exact (fun h0 : term373 k p n => @lem195792 k m p n h1 h2 h3 h4 h5). Qed.
Lemma lem195795 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem195796 (k : nat) (p : nat) (n : nat) : (term410 k p n) = (term259 k p n).
Proof. exact (@lem195795 (term259 k p n)). Qed.
Lemma lem195797 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : term259 k p n.
Proof. exact (EQ_MP (@lem195796 k p n) (@lem195793 k m p n h1 h2 h3 h4 h5)). Qed.
Lemma lem195800 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem195802 (k : nat) (p : nat) (n : nat) : (term373 k p n) = (term411 k p n).
Proof. exact (@lem195800 (term259 k p n)). Qed.
Lemma lem195805 (m : nat) (k : nat) (p : nat) (n : nat) (h1 : term326 m k p n) : term411 k p n.
Proof. exact (EQ_MP (@lem195802 k p n) (@lem195504 m k p n h1)). Qed.
Lemma lem195808 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : False.
Proof. exact (@lem195805 m k p n h4 (@lem195797 k m p n h1 h2 h3 h4 h5)). Qed.
Lemma lem195809 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : term208.
Proof. exact (fun h0 : ~ False => @lem195808 k m p n h1 h2 h3 h4 h5). Qed.
Lemma lem195811 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem195812 : term208 = False.
Proof. exact (@lem195811 False). Qed.
Lemma lem195813 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195812) (@lem195809 k m p n h1 h2 h3 h4 h5)). Qed.
Lemma lem195814 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : (term214 m p n) = False.
Proof. exact (prop_ext (fun h6 : term214 m p n => @lem195813 k m p n h1 h2 h3 h4 h5) (fun h6 : False => @lem195472 m p n h5)). Qed.
Lemma lem195815 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195814 k m p n h1 h2 h3 h4 h5) (@lem195472 m p n h5)). Qed.
Lemma lem195816 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : (term214 m p n) = False.
Proof. exact (prop_ext (fun h6 : term214 m p n => @lem195815 k m p n h1 h2 h3 h4 h5) (fun h6 : False => @lem195360 m p n h5)). Qed.
Lemma lem195817 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195816 k m p n h1 h2 h3 h4 h5) (@lem195360 m p n h5)). Qed.
Lemma lem195818 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : term42 = False.
Proof. exact (prop_ext (fun h6 : term42 => @lem195817 k m p n h1 h2 h3 h4 h5) (fun h6 : False => @lem195430 h3)). Qed.
Lemma lem195819 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195818 k m p n h1 h2 h3 h4 h5) (@lem195430 h3)). Qed.
Lemma lem195820 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : (term214 m p n) = False.
Proof. exact (prop_ext (fun h6 : term214 m p n => @lem195819 k m p n h1 h2 h3 h4 h5) (fun h6 : False => @lem195360 m p n h5)). Qed.
Lemma lem195821 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195820 k m p n h1 h2 h3 h4 h5) (@lem195360 m p n h5)). Qed.
Lemma lem195822 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : (term326 m k p n) = False.
Proof. exact (prop_ext (fun h6 : term326 m k p n => @lem195821 k m p n h1 h2 h3 h4 h5) (fun h6 : False => @lem195350 m k p n h4)). Qed.
Lemma lem195823 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195822 k m p n h1 h2 h3 h4 h5) (@lem195350 m k p n h4)). Qed.
Lemma lem195824 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : term42 = False.
Proof. exact (prop_ext (fun h6 : term42 => @lem195823 k m p n h1 h2 h3 h4 h5) (fun h6 : False => @lem195322 h3)). Qed.
Lemma lem195825 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195824 k m p n h1 h2 h3 h4 h5) (@lem195322 h3)). Qed.
Lemma lem195826 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : (term214 m p n) = False.
Proof. exact (prop_ext (fun h6 : term214 m p n => @lem195825 k m p n h1 h2 h3 h4 h5) (fun h6 : False => @lem195212 m p n h5)). Qed.
Lemma lem195827 (k : nat) (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term326 m k p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195826 k m p n h1 h2 h3 h4 h5) (@lem195212 m p n h5)). Qed.
Lemma lem195828 (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term269 m p n) (h5 : term214 m p n) : False.
Proof. exact (ex_elim (@lem194985 m p n h4) (fun k : nat => fun h0 : term333 m p n k => @lem195827 k m p n h1 h2 h3 h0 h5)). Qed.
Lemma lem195829 (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term269 m p n) (h5 : term214 m p n) : term42 = False.
Proof. exact (prop_ext (fun h6 : term42 => @lem195828 m p n h1 h2 h3 h4 h5) (fun h6 : False => @lem195191 h3)). Qed.
Lemma lem195830 (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term269 m p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195829 m p n h1 h2 h3 h4 h5) (@lem195191 h3)). Qed.
Lemma lem195831 (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term269 m p n) (h5 : term214 m p n) : (term214 m p n) = False.
Proof. exact (prop_ext (fun h6 : term214 m p n => @lem195830 m p n h1 h2 h3 h4 h5) (fun h6 : False => @lem194915 m p n h5)). Qed.
Lemma lem195832 (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term42) (h4 : term269 m p n) (h5 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195831 m p n h1 h2 h3 h4 h5) (@lem194915 m p n h5)). Qed.
Lemma lem195833 (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term269 m p n) (h4 : term214 m p n) : term274.
Proof. exact (fun h0 : term42 => @lem195832 m p n h1 h2 h0 h3 h4). Qed.
Lemma lem195834 : term274 = term275.
Proof. exact (@lem69 term42). Qed.
Lemma lem195835 (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term311) (h3 : term269 m p n) (h4 : term214 m p n) : term275.
Proof. exact (EQ_MP (@lem195834) (@lem195833 m p n h1 h2 h3 h4)). Qed.
Lemma lem195836 (m : nat) (p : nat) (n : nat) (h1 : term320) (h2 : term269 m p n) (h3 : term214 m p n) : term278.
Proof. exact (fun h0 : term311 => @lem195835 m p n h1 h0 h2 h3). Qed.
Lemma lem195837 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) (h2 : term214 m p n) : term281.
Proof. exact (fun h0 : term320 => @lem195836 m p n h0 h1 h2). Qed.
Lemma lem195838 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) (h2 : term214 m p n) : term284.
Proof. exact (fun h0 : term324 => @lem195837 m p n h1 h2). Qed.
Lemma lem195839 (m : nat) (p : nat) (n : nat) (h1 : term214 m p n) : term287 m p n.
Proof. exact (fun h0 : term269 m p n => @lem195838 m p n h0 h1). Qed.
Lemma lem195840 (m : nat) (p : nat) (n : nat) : term290 m p n.
Proof. exact (fun h0 : term214 m p n => @lem195839 m p n h0). Qed.
Lemma lem195841 (m : nat) (p : nat) (n : nat) : term292 m p n.
Proof. exact (fun h0 : term215 p => @lem195840 m p n). Qed.
Lemma lem195846 (p : nat) (n : nat) : term296 p n.
Proof. exact (fun m : nat => @lem195841 m p n). Qed.
Lemma lem195851 (n : nat) : term300 n.
Proof. exact (fun p : nat => @lem195846 p n). Qed.
Lemma lem195856 : term304.
Proof. exact (fun n : nat => @lem195851 n). Qed.
Lemma lem195857 : term303.
Proof. exact (EQ_MP (@lem194896) (@lem195856)). Qed.
Lemma lem195858 (n : nat) : term412 n.
Proof. exact (@lem195857 n). Qed.
Lemma lem195859 (n : nat) : (term412 n) = (term299 n).
Proof. exact (eq_refl (term412 n)). Qed.
Lemma lem195860 (n : nat) : term299 n.
Proof. exact (EQ_MP (@lem195859 n) (@lem195858 n)). Qed.
Lemma lem195861 (n : nat) (p : nat) : term413 n p.
Proof. exact (@lem195860 n p). Qed.
Lemma lem195862 (p : nat) (n : nat) : (term413 n p) = (term295 p n).
Proof. exact (eq_refl (term413 n p)). Qed.
Lemma lem195863 (p : nat) (n : nat) : term295 p n.
Proof. exact (EQ_MP (@lem195862 p n) (@lem195861 n p)). Qed.
Lemma lem195864 (p : nat) (n : nat) (m : nat) : term414 p n m.
Proof. exact (@lem195863 p n m). Qed.
Lemma lem195865 (m : nat) (p : nat) (n : nat) : (term414 p n m) = (term270 m p n).
Proof. exact (eq_refl (term414 p n m)). Qed.
Lemma lem195866 (m : nat) (p : nat) (n : nat) : term270 m p n.
Proof. exact (EQ_MP (@lem195865 m p n) (@lem195864 p n m)). Qed.
Lemma lem195868 (m : nat) (p : nat) (n : nat) : term270 m p n.
Proof. exact (@lem194563 m p n (@lem195866 m p n)). Qed.
Lemma lem195869 (m : nat) (n : nat) (p : nat) (h1 : term215 p) : term289 m p n.
Proof. exact (@lem195868 m p n (@lem194324 p h1)). Qed.
Lemma lem195870 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term214 m p n) : term286 m p n.
Proof. exact (@lem195869 m n p h1 (@lem194323 m p n h2)). Qed.
Lemma lem195871 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) (h2 : term215 p) (h3 : term214 m p n) : term283.
Proof. exact (@lem195870 m p n h2 h3 (@lem194548 m p n h1)). Qed.
Lemma lem195872 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) (h2 : term215 p) (h3 : term214 m p n) : term280.
Proof. exact (@lem195871 m p n h1 h2 h3 (@lem77775)). Qed.
Lemma lem195873 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) (h2 : term215 p) (h3 : term214 m p n) : term277.
Proof. exact (@lem195872 m p n h1 h2 h3 (@lem101399)). Qed.
Lemma lem195874 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) (h2 : term215 p) (h3 : term214 m p n) : term274.
Proof. exact (@lem195873 m p n h1 h2 h3 (@lem93743)). Qed.
Lemma lem195875 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) (h2 : term215 p) (h3 : term214 m p n) : False.
Proof. exact (@lem195874 m p n h1 h2 h3 (@lem91603)). Qed.
Lemma lem195876 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) (h2 : term215 p) (h3 : term214 m p n) : (term269 m p n) = False.
Proof. exact (prop_ext (fun h4 : term269 m p n => @lem195875 m p n h1 h2 h3) (fun h4 : False => @lem194548 m p n h1)). Qed.
Lemma lem195877 (m : nat) (p : nat) (n : nat) (h1 : term269 m p n) (h2 : term215 p) (h3 : term214 m p n) : False.
Proof. exact (EQ_MP (@lem195876 m p n h1 h2 h3) (@lem194548 m p n h1)). Qed.
Lemma lem195878 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term214 m p n) : term268 m p n.
Proof. exact (fun h0 : term269 m p n => @lem195877 m p n h0 h1 h2). Qed.
Lemma lem195879 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term214 m p n) : term267 m p n.
Proof. exact (EQ_MP (@lem194547 m p n) (@lem195878 m p n h1 h2)). Qed.
Lemma lem195880 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term214 m p n) : term266 m n p.
Proof. exact (EQ_MP (@lem194543 m n p h1) (@lem195879 m p n h1 h2)). Qed.
Lemma lem195881 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term214 m p n) : term415 m n p.
Proof. exact (@lem194327 m n p (@lem195880 m p n h1 h2)). Qed.
Lemma lem195882 (m : nat) (p : nat) (n : nat) (h1 : term213 m p n) : term214 m p n.
Proof. exact (proj2 (@lem194322 m p n h1)). Qed.
Lemma lem195883 (m : nat) (p : nat) (n : nat) (h1 : term213 m p n) : term215 p.
Proof. exact (proj1 (@lem194322 m p n h1)). Qed.
Lemma lem195884 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term214 m p n) : (term214 m p n) = (term415 m n p).
Proof. exact (prop_ext (fun h3 : term214 m p n => @lem195881 m p n h1 h2) (fun h3 : term415 m n p => @lem194323 m p n h2)). Qed.
Lemma lem195885 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term214 m p n) : term415 m n p.
Proof. exact (EQ_MP (@lem195884 m p n h1 h2) (@lem194323 m p n h2)). Qed.
Lemma lem195886 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term214 m p n) : (term215 p) = (term415 m n p).
Proof. exact (prop_ext (fun h3 : term215 p => @lem195885 m p n h1 h2) (fun h3 : term415 m n p => @lem194324 p h1)). Qed.
Lemma lem195887 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term214 m p n) : term415 m n p.
Proof. exact (EQ_MP (@lem195886 m p n h1 h2) (@lem194324 p h1)). Qed.
Lemma lem195888 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term213 m p n) : (term214 m p n) = (term415 m n p).
Proof. exact (prop_ext (fun h3 : term214 m p n => @lem195887 m p n h1 h3) (fun h3 : term415 m n p => @lem195882 m p n h2)). Qed.
Lemma lem195889 (m : nat) (p : nat) (n : nat) (h1 : term215 p) (h2 : term213 m p n) : term415 m n p.
Proof. exact (EQ_MP (@lem195888 m p n h1 h2) (@lem195882 m p n h2)). Qed.
Lemma lem195890 (m : nat) (p : nat) (n : nat) (h1 : term213 m p n) : (term215 p) = (term415 m n p).
Proof. exact (prop_ext (fun h2 : term215 p => @lem195889 m p n h2 h1) (fun h2 : term415 m n p => @lem195883 m p n h1)). Qed.
Lemma lem195891 (m : nat) (p : nat) (n : nat) (h1 : term213 m p n) : term415 m n p.
Proof. exact (EQ_MP (@lem195890 m p n h1) (@lem195883 m p n h1)). Qed.
Lemma lem195892 (m : nat) (n : nat) (p : nat) : term416 m n p.
Proof. exact (fun h0 : term213 m p n => @lem195891 m p n h0). Qed.
Lemma lem195897 (m : nat) (n : nat) : term417 m n.
Proof. exact (fun p : nat => @lem195892 m n p). Qed.
Lemma lem195902 (m : nat) : term418 m.
Proof. exact (fun n : nat => @lem195897 m n). Qed.
Lemma lem195907 : term419.
Proof. exact (fun m : nat => @lem195902 m). Qed.
