Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_SING_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3266967 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3266968 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3266967 A s t). Qed.
Lemma lem3266969 {A : Type'} (s : A -> Prop) (a : A) : (term0 A s a) = ((term1 A s a) = (@EMPTY A)).
Proof. exact (@lem3266968 A s (@INSERT A a (@EMPTY A))). Qed.
Lemma lem3266973 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3266974 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (@lem3266973 A s t). Qed.
Lemma lem3266975 {A : Type'} (s : A -> Prop) (a : A) : ((term1 A s a) = (@EMPTY A)) = (term3 A s a).
Proof. exact (@lem3266974 A (term1 A s a) (@EMPTY A)). Qed.
Lemma lem3266980 {A : Type'} (s : A -> Prop) (a : A) : (term0 A s a) = (term3 A s a).
Proof. exact (TRANS (@lem3266969 A s a) (@lem3266975 A s a)). Qed.
Lemma lem3266985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3266986 {A : Type'} (s : A -> Prop) (a : A) : (term4 A s a) = (term5 A s a).
Proof. exact (MK_COMB (@lem3266985) (@lem3266980 A s a)). Qed.
Lemma lem3266987 {A : Type'} (a : A) (s : A -> Prop) : (term6 A a s) = (term6 A a s).
Proof. exact (eq_refl (term6 A a s)). Qed.
Lemma lem3266988 {A : Type'} (a : A) (s : A -> Prop) : ((term0 A s a) = (term6 A a s)) = ((term3 A s a) = (term6 A a s)).
Proof. exact (MK_COMB (@lem3266986 A s a) (@lem3266987 A a s)). Qed.
Lemma lem3266993 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (fun_ext (fun a : A => @lem3266988 A a s)). Qed.
Lemma lem3266994 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266995 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (MK_COMB (@lem3266994 A) (@lem3266993 A s)). Qed.
Lemma lem3267000 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3266995 A s)). Qed.
Lemma lem3267001 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3267002 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3267001 A) (@lem3267000 A)). Qed.
Lemma lem3267007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3267008 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem3267007) (@lem3267002 A)). Qed.
Lemma lem3267022 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3267023 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3267022 A s t). Qed.
Lemma lem3267024 {A : Type'} (a : A) (s : A -> Prop) : (term17 A a s) = ((term18 A a s) = (@EMPTY A)).
Proof. exact (@lem3267023 A (@INSERT A a (@EMPTY A)) s). Qed.
Lemma lem3267028 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3267029 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (@lem3267028 A s t). Qed.
Lemma lem3267030 {A : Type'} (a : A) (s : A -> Prop) : ((term18 A a s) = (@EMPTY A)) = (term19 A a s).
Proof. exact (@lem3267029 A (term18 A a s) (@EMPTY A)). Qed.
Lemma lem3267035 {A : Type'} (a : A) (s : A -> Prop) : (term17 A a s) = (term19 A a s).
Proof. exact (TRANS (@lem3267024 A a s) (@lem3267030 A a s)). Qed.
Lemma lem3267040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267041 {A : Type'} (a : A) (s : A -> Prop) : (term20 A a s) = (term21 A a s).
Proof. exact (MK_COMB (@lem3267040) (@lem3267035 A a s)). Qed.
Lemma lem3267042 {A : Type'} (a : A) (s : A -> Prop) : (term6 A a s) = (term6 A a s).
Proof. exact (eq_refl (term6 A a s)). Qed.
Lemma lem3267043 {A : Type'} (a : A) (s : A -> Prop) : ((term17 A a s) = (term6 A a s)) = ((term19 A a s) = (term6 A a s)).
Proof. exact (MK_COMB (@lem3267041 A a s) (@lem3267042 A a s)). Qed.
Lemma lem3267048 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (fun_ext (fun a : A => @lem3267043 A a s)). Qed.
Lemma lem3267049 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267050 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (MK_COMB (@lem3267049 A) (@lem3267048 A s)). Qed.
Lemma lem3267055 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267050 A s)). Qed.
Lemma lem3267056 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3267057 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem3267056 A) (@lem3267055 A)). Qed.
Lemma lem3267062 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (MK_COMB (@lem3267008 A) (@lem3267057 A)). Qed.
Lemma lem3267065 {A : Type'} : (term31 A) = (term30 A).
Proof. exact (SYM (@lem3267062 A)). Qed.
Lemma lem3267085 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term33 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3267086 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term33 A s x t).
Proof. exact (@lem3267085 A s x t). Qed.
Lemma lem3267087 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term34 A x s a) = (term35 A s x a).
Proof. exact (@lem3267086 A s x (@INSERT A a (@EMPTY A))). Qed.
Lemma lem3267091 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3267092 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3267091 A P x). Qed.
Lemma lem3267093 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3267092 A s x). Qed.
Lemma lem3267094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3267095 {A : Type'} (s : A -> Prop) (x : A) : (term36 A x s) = (term37 A s x).
Proof. exact (MK_COMB (@lem3267094) (@lem3267093 A s x)). Qed.
Lemma lem3267097 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term38 A x y s) = (term39 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3267098 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term38 A x y s) = (term39 A y x s).
Proof. exact (@lem3267097 A y x s). Qed.
Lemma lem3267099 {A : Type'} (a : A) (x : A) : (term40 A x a) = (term41 A a x).
Proof. exact (@lem3267098 A a x (@EMPTY A)). Qed.
Lemma lem3267105 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3267106 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3267105 A x). Qed.
Lemma lem3267107 {A : Type'} (x : A) (a : A) : (term42 A x a) = (term42 A x a).
Proof. exact (eq_refl (term42 A x a)). Qed.
Lemma lem3267108 {A : Type'} (x : A) (a : A) : (term41 A a x) = (term43 A x a).
Proof. exact (MK_COMB (@lem3267107 A x a) (@lem3267106 A x)). Qed.
Lemma lem3267110 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3267111 {A : Type'} (x : A) (a : A) : (term43 A x a) = (x = a).
Proof. exact (@lem3267110 (x = a)). Qed.
Lemma lem3267114 {A : Type'} (x : A) (a : A) : (term41 A a x) = (x = a).
Proof. exact (TRANS (@lem3267108 A x a) (@lem3267111 A x a)). Qed.
Lemma lem3267115 {A : Type'} (x : A) (a : A) : (term40 A x a) = (x = a).
Proof. exact (TRANS (@lem3267099 A a x) (@lem3267114 A x a)). Qed.
Lemma lem3267116 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term35 A s x a) = (term44 A s x a).
Proof. exact (MK_COMB (@lem3267095 A s x) (@lem3267115 A x a)). Qed.
Lemma lem3267119 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term34 A x s a) = (term44 A s x a).
Proof. exact (TRANS (@lem3267087 A s x a) (@lem3267116 A s x a)). Qed.
Lemma lem3267120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267121 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term45 A x s a) = (term46 A s x a).
Proof. exact (MK_COMB (@lem3267120) (@lem3267119 A s x a)). Qed.
Lemma lem3267123 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3267124 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3267123 A x). Qed.
Lemma lem3267125 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((term34 A x s a) = (@IN A x (@EMPTY A))) = ((term44 A s x a) = False).
Proof. exact (MK_COMB (@lem3267121 A s x a) (@lem3267124 A x)). Qed.
Lemma lem3267127 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3267128 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((term44 A s x a) = False) = (term47 A s x a).
Proof. exact (@lem3267127 (term44 A s x a)). Qed.
Lemma lem3267133 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((term34 A x s a) = (@IN A x (@EMPTY A))) = (term47 A s x a).
Proof. exact (TRANS (@lem3267125 A s x a) (@lem3267128 A s x a)). Qed.
Lemma lem3267134 {A : Type'} (s : A -> Prop) (a : A) : (term48 A s a) = (term49 A s a).
Proof. exact (fun_ext (fun x : A => @lem3267133 A s x a)). Qed.
Lemma lem3267135 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267136 {A : Type'} (s : A -> Prop) (a : A) : (term3 A s a) = (term50 A s a).
Proof. exact (MK_COMB (@lem3267135 A) (@lem3267134 A s a)). Qed.
Lemma lem3267141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267142 {A : Type'} (s : A -> Prop) (a : A) : (term5 A s a) = (term51 A s a).
Proof. exact (MK_COMB (@lem3267141) (@lem3267136 A s a)). Qed.
Lemma lem3267144 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3267145 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3267144 A P x). Qed.
Lemma lem3267146 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem3267145 A s a). Qed.
Lemma lem3267147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3267148 {A : Type'} (s : A -> Prop) (a : A) : (term6 A a s) = (term52 A s a).
Proof. exact (MK_COMB (@lem3267147) (@lem3267146 A s a)). Qed.
Lemma lem3267149 {A : Type'} (s : A -> Prop) (a : A) : ((term3 A s a) = (term6 A a s)) = ((term50 A s a) = (term52 A s a)).
Proof. exact (MK_COMB (@lem3267142 A s a) (@lem3267148 A s a)). Qed.
Lemma lem3267152 {A : Type'} (s : A -> Prop) : (term8 A s) = (term53 A s).
Proof. exact (fun_ext (fun a : A => @lem3267149 A s a)). Qed.
Lemma lem3267153 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267154 {A : Type'} (s : A -> Prop) : (term10 A s) = (term54 A s).
Proof. exact (MK_COMB (@lem3267153 A) (@lem3267152 A s)). Qed.
Lemma lem3267159 {A : Type'} : (term12 A) = (term55 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267154 A s)). Qed.
Lemma lem3267160 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3267161 {A : Type'} : (term14 A) = (term56 A).
Proof. exact (MK_COMB (@lem3267160 A) (@lem3267159 A)). Qed.
Lemma lem3267166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3267167 {A : Type'} : (term16 A) = (term57 A).
Proof. exact (MK_COMB (@lem3267166) (@lem3267161 A)). Qed.
Lemma lem3267185 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term33 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3267186 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term33 A s x t).
Proof. exact (@lem3267185 A s x t). Qed.
Lemma lem3267187 {A : Type'} (a : A) (x : A) (s : A -> Prop) : (term58 A x a s) = (term59 A a x s).
Proof. exact (@lem3267186 A (@INSERT A a (@EMPTY A)) x s). Qed.
Lemma lem3267191 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term38 A x y s) = (term39 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3267192 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term38 A x y s) = (term39 A y x s).
Proof. exact (@lem3267191 A y x s). Qed.
Lemma lem3267193 {A : Type'} (a : A) (x : A) : (term40 A x a) = (term41 A a x).
Proof. exact (@lem3267192 A a x (@EMPTY A)). Qed.
Lemma lem3267199 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3267200 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3267199 A x). Qed.
Lemma lem3267201 {A : Type'} (x : A) (a : A) : (term42 A x a) = (term42 A x a).
Proof. exact (eq_refl (term42 A x a)). Qed.
Lemma lem3267202 {A : Type'} (x : A) (a : A) : (term41 A a x) = (term43 A x a).
Proof. exact (MK_COMB (@lem3267201 A x a) (@lem3267200 A x)). Qed.
Lemma lem3267204 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3267205 {A : Type'} (x : A) (a : A) : (term43 A x a) = (x = a).
Proof. exact (@lem3267204 (x = a)). Qed.
Lemma lem3267208 {A : Type'} (x : A) (a : A) : (term41 A a x) = (x = a).
Proof. exact (TRANS (@lem3267202 A x a) (@lem3267205 A x a)). Qed.
Lemma lem3267209 {A : Type'} (x : A) (a : A) : (term40 A x a) = (x = a).
Proof. exact (TRANS (@lem3267193 A a x) (@lem3267208 A x a)). Qed.
Lemma lem3267210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3267211 {A : Type'} (x : A) (a : A) : (term60 A x a) = (term61 A x a).
Proof. exact (MK_COMB (@lem3267210) (@lem3267209 A x a)). Qed.
Lemma lem3267213 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3267214 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3267213 A P x). Qed.
Lemma lem3267215 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3267214 A s x). Qed.
Lemma lem3267216 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term59 A a x s) = (term62 A a s x).
Proof. exact (MK_COMB (@lem3267211 A x a) (@lem3267215 A s x)). Qed.
Lemma lem3267219 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term58 A x a s) = (term62 A a s x).
Proof. exact (TRANS (@lem3267187 A a x s) (@lem3267216 A a s x)). Qed.
Lemma lem3267220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267221 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term63 A x a s) = (term64 A a s x).
Proof. exact (MK_COMB (@lem3267220) (@lem3267219 A a s x)). Qed.
Lemma lem3267223 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3267224 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3267223 A x). Qed.
Lemma lem3267225 {A : Type'} (a : A) (s : A -> Prop) (x : A) : ((term58 A x a s) = (@IN A x (@EMPTY A))) = ((term62 A a s x) = False).
Proof. exact (MK_COMB (@lem3267221 A a s x) (@lem3267224 A x)). Qed.
Lemma lem3267227 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3267228 {A : Type'} (a : A) (s : A -> Prop) (x : A) : ((term62 A a s x) = False) = (term65 A a s x).
Proof. exact (@lem3267227 (term62 A a s x)). Qed.
Lemma lem3267233 {A : Type'} (a : A) (s : A -> Prop) (x : A) : ((term58 A x a s) = (@IN A x (@EMPTY A))) = (term65 A a s x).
Proof. exact (TRANS (@lem3267225 A a s x) (@lem3267228 A a s x)). Qed.
Lemma lem3267234 {A : Type'} (a : A) (s : A -> Prop) : (term66 A a s) = (term67 A a s).
Proof. exact (fun_ext (fun x : A => @lem3267233 A a s x)). Qed.
Lemma lem3267235 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267236 {A : Type'} (a : A) (s : A -> Prop) : (term19 A a s) = (term68 A a s).
Proof. exact (MK_COMB (@lem3267235 A) (@lem3267234 A a s)). Qed.
Lemma lem3267241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267242 {A : Type'} (a : A) (s : A -> Prop) : (term21 A a s) = (term69 A a s).
Proof. exact (MK_COMB (@lem3267241) (@lem3267236 A a s)). Qed.
Lemma lem3267244 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3267245 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3267244 A P x). Qed.
Lemma lem3267246 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem3267245 A s a). Qed.
Lemma lem3267247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3267248 {A : Type'} (s : A -> Prop) (a : A) : (term6 A a s) = (term52 A s a).
Proof. exact (MK_COMB (@lem3267247) (@lem3267246 A s a)). Qed.
Lemma lem3267249 {A : Type'} (s : A -> Prop) (a : A) : ((term19 A a s) = (term6 A a s)) = ((term68 A a s) = (term52 A s a)).
Proof. exact (MK_COMB (@lem3267242 A a s) (@lem3267248 A s a)). Qed.
Lemma lem3267252 {A : Type'} (s : A -> Prop) : (term23 A s) = (term70 A s).
Proof. exact (fun_ext (fun a : A => @lem3267249 A s a)). Qed.
Lemma lem3267253 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267254 {A : Type'} (s : A -> Prop) : (term25 A s) = (term71 A s).
Proof. exact (MK_COMB (@lem3267253 A) (@lem3267252 A s)). Qed.
Lemma lem3267259 {A : Type'} : (term27 A) = (term72 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267254 A s)). Qed.
Lemma lem3267260 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3267261 {A : Type'} : (term29 A) = (term73 A).
Proof. exact (MK_COMB (@lem3267260 A) (@lem3267259 A)). Qed.
Lemma lem3267266 {A : Type'} : (term31 A) = (term74 A).
Proof. exact (MK_COMB (@lem3267167 A) (@lem3267261 A)). Qed.
Lemma lem3267269 {A : Type'} : (term74 A) = (term31 A).
Proof. exact (SYM (@lem3267266 A)). Qed.
Lemma lem3267271 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3267272 {A : Type'} : (term74 A) = (term76 A).
Proof. exact (@lem3267271 (term74 A)). Qed.
Lemma lem3267273 {A : Type'} : (term76 A) = (term74 A).
Proof. exact (SYM (@lem3267272 A)). Qed.
Lemma lem3267274 {A : Type'} (h1 : term77 A) : term77 A.
Proof. exact (h1). Qed.
Lemma lem3267277 {A : Type'} (h1 : term76 A) : term76 A.
Proof. exact (h1). Qed.
Lemma lem3267278 {A : Type'} : term78 A.
Proof. exact (fun h0 : term76 A => @lem3267277 A h0). Qed.
Lemma lem3267279 {A : Type'} (h1 : term78 A) : term78 A.
Proof. exact (h1). Qed.
Lemma lem3267280 {A : Type'} (h1 : term76 A) : term76 A.
Proof. exact (h1). Qed.
Lemma lem3267281 {A : Type'} (h1 : term76 A) (h2 : term78 A) : term76 A.
Proof. exact (@lem3267279 A h2 (@lem3267280 A h1)). Qed.
Lemma lem3267282 {A : Type'} (h1 : term76 A) : term79 A.
Proof. exact (fun h0 : term78 A => @lem3267281 A h1 h0). Qed.
Lemma lem3267283 {A : Type'} (h1 : term78 A) : term78 A.
Proof. exact (h1). Qed.
Lemma lem3267284 {A : Type'} (h1 : term76 A) (h2 : term78 A) : term76 A.
Proof. exact (@lem3267282 A h1 (@lem3267283 A h2)). Qed.
Lemma lem3267285 {A : Type'} (h1 : term78 A) : term78 A.
Proof. exact (fun h0 : term76 A => @lem3267284 A h0 h1). Qed.
Lemma lem3267286 {A : Type'} : term80 A.
Proof. exact (fun h0 : term78 A => @lem3267285 A h0). Qed.
Lemma lem3267289 {A : Type'} : term78 A.
Proof. exact (@lem3267286 A (@lem3267278 A)). Qed.
Lemma lem3267290 {A : Type'} : term78 A.
Proof. exact (@lem3267289 A). Qed.
Lemma lem3267292 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3267293 {A : Type'} : (term76 A) = (term81 A).
Proof. exact (@lem3267292 (term77 A)). Qed.
Lemma lem3267295 (t : Prop) : (term82 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3267296 {A : Type'} : (term81 A) = (term74 A).
Proof. exact (@lem3267295 (term74 A)). Qed.
Lemma lem3267331 {A : Type'} : (term76 A) = (term74 A).
Proof. exact (TRANS (@lem3267293 A) (@lem3267296 A)). Qed.
Lemma lem3267334 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term52 A s a).
Proof. exact (eq_refl (term52 A s a)). Qed.
Lemma lem3267341 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term65 A a s x) = (term65 A a s x).
Proof. exact (eq_refl (term65 A a s x)). Qed.
Lemma lem3267342 {A : Type'} (a : A) (s : A -> Prop) : (term67 A a s) = (term67 A a s).
Proof. exact (fun_ext (fun x : A => @lem3267341 A a s x)). Qed.
Lemma lem3267343 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267344 {A : Type'} (a : A) (s : A -> Prop) : (term68 A a s) = (term68 A a s).
Proof. exact (MK_COMB (@lem3267343 A) (@lem3267342 A a s)). Qed.
Lemma lem3267345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267346 {A : Type'} (a : A) (s : A -> Prop) : (term69 A a s) = (term69 A a s).
Proof. exact (MK_COMB (@lem3267345) (@lem3267344 A a s)). Qed.
Lemma lem3267347 {A : Type'} (s : A -> Prop) (a : A) : ((term68 A a s) = (term52 A s a)) = ((term68 A a s) = (term52 A s a)).
Proof. exact (MK_COMB (@lem3267346 A a s) (@lem3267334 A s a)). Qed.
Lemma lem3267348 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (fun_ext (fun a : A => @lem3267347 A s a)). Qed.
Lemma lem3267349 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267350 {A : Type'} (s : A -> Prop) : (term71 A s) = (term71 A s).
Proof. exact (MK_COMB (@lem3267349 A) (@lem3267348 A s)). Qed.
Lemma lem3267351 {A : Type'} : (term72 A) = (term72 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267350 A s)). Qed.
Lemma lem3267352 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3267353 {A : Type'} : (term73 A) = (term73 A).
Proof. exact (MK_COMB (@lem3267352 A) (@lem3267351 A)). Qed.
Lemma lem3267356 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term52 A s a).
Proof. exact (eq_refl (term52 A s a)). Qed.
Lemma lem3267363 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term47 A s x a) = (term47 A s x a).
Proof. exact (eq_refl (term47 A s x a)). Qed.
Lemma lem3267364 {A : Type'} (s : A -> Prop) (a : A) : (term49 A s a) = (term49 A s a).
Proof. exact (fun_ext (fun x : A => @lem3267363 A s x a)). Qed.
Lemma lem3267365 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267366 {A : Type'} (s : A -> Prop) (a : A) : (term50 A s a) = (term50 A s a).
Proof. exact (MK_COMB (@lem3267365 A) (@lem3267364 A s a)). Qed.
Lemma lem3267367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267368 {A : Type'} (s : A -> Prop) (a : A) : (term51 A s a) = (term51 A s a).
Proof. exact (MK_COMB (@lem3267367) (@lem3267366 A s a)). Qed.
Lemma lem3267369 {A : Type'} (s : A -> Prop) (a : A) : ((term50 A s a) = (term52 A s a)) = ((term50 A s a) = (term52 A s a)).
Proof. exact (MK_COMB (@lem3267368 A s a) (@lem3267356 A s a)). Qed.
Lemma lem3267370 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (fun_ext (fun a : A => @lem3267369 A s a)). Qed.
Lemma lem3267371 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267372 {A : Type'} (s : A -> Prop) : (term54 A s) = (term54 A s).
Proof. exact (MK_COMB (@lem3267371 A) (@lem3267370 A s)). Qed.
Lemma lem3267373 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267372 A s)). Qed.
Lemma lem3267374 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3267375 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (MK_COMB (@lem3267374 A) (@lem3267373 A)). Qed.
Lemma lem3267376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3267377 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (MK_COMB (@lem3267376) (@lem3267375 A)). Qed.
Lemma lem3267378 {A : Type'} : (term74 A) = (term74 A).
Proof. exact (MK_COMB (@lem3267377 A) (@lem3267353 A)). Qed.
Lemma lem3267423 {A : Type'} : (term76 A) = (term74 A).
Proof. exact (TRANS (@lem3267331 A) (@lem3267378 A)). Qed.
Lemma lem3267424 {A : Type'} : (term74 A) = (term76 A).
Proof. exact (SYM (@lem3267423 A)). Qed.
Lemma lem3267426 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3267427 {A : Type'} : (term74 A) = (term76 A).
Proof. exact (@lem3267426 (term74 A)). Qed.
Lemma lem3267428 {A : Type'} : (term76 A) = (term74 A).
Proof. exact (SYM (@lem3267427 A)). Qed.
Lemma lem3267429 {A : Type'} (h1 : term77 A) : term77 A.
Proof. exact (h1). Qed.
Lemma lem3267438 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term47 A s x a) = (term83 A s x a).
Proof. exact (@lem17045 (s x) (x = a)). Qed.
Lemma lem3267443 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term84 A s x a) = (term44 A s x a).
Proof. exact (@lem16933 (term44 A s x a)). Qed.
Lemma lem3267444 {A : Type'} (P : A -> Prop) : (term85 A P) = (term86 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3267445 {A : Type'} (s : A -> Prop) (a : A) : (term87 A s a) = (term88 A s a).
Proof. exact (@lem3267444 A (term49 A s a)). Qed.
Lemma lem3267446 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term89 A s a x) = (term47 A s x a).
Proof. exact (eq_refl (term89 A s a x)). Qed.
Lemma lem3267447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3267448 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term90 A s a x) = (term84 A s x a).
Proof. exact (MK_COMB (@lem3267447) (@lem3267446 A s x a)). Qed.
Lemma lem3267449 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term90 A s a x) = (term44 A s x a).
Proof. exact (TRANS (@lem3267448 A s x a) (@lem3267443 A s x a)). Qed.
Lemma lem3267450 {A : Type'} (s : A -> Prop) (a : A) : (term91 A s a) = (term92 A s a).
Proof. exact (fun_ext (fun x : A => @lem3267449 A s x a)). Qed.
Lemma lem3267451 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267452 {A : Type'} (s : A -> Prop) (a : A) : (term88 A s a) = (term93 A s a).
Proof. exact (MK_COMB (@lem3267451 A) (@lem3267450 A s a)). Qed.
Lemma lem3267453 {A : Type'} (s : A -> Prop) (a : A) : (term87 A s a) = (term93 A s a).
Proof. exact (TRANS (@lem3267445 A s a) (@lem3267452 A s a)). Qed.
Lemma lem3267454 {A : Type'} (s : A -> Prop) (a : A) : (term49 A s a) = (term94 A s a).
Proof. exact (fun_ext (fun x : A => @lem3267438 A s x a)). Qed.
Lemma lem3267455 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267456 {A : Type'} (s : A -> Prop) (a : A) : (term50 A s a) = (term95 A s a).
Proof. exact (MK_COMB (@lem3267455 A) (@lem3267454 A s a)). Qed.
Lemma lem3267457 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term52 A s a).
Proof. exact (eq_refl (term52 A s a)). Qed.
Lemma lem3267460 {A : Type'} (s : A -> Prop) (a : A) : (term96 A s a) = (s a).
Proof. exact (@lem16933 (s a)). Qed.
Lemma lem3267461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3267462 {A : Type'} (s : A -> Prop) (a : A) : (term97 A s a) = (term98 A s a).
Proof. exact (MK_COMB (@lem3267461) (@lem3267453 A s a)). Qed.
Lemma lem3267463 {A : Type'} (s : A -> Prop) (a : A) : (term99 A s a) = (term100 A s a).
Proof. exact (MK_COMB (@lem3267462 A s a) (@lem3267457 A s a)). Qed.
Lemma lem3267464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3267465 {A : Type'} (s : A -> Prop) (a : A) : (term101 A s a) = (term102 A s a).
Proof. exact (MK_COMB (@lem3267464) (@lem3267456 A s a)). Qed.
Lemma lem3267466 {A : Type'} (s : A -> Prop) (a : A) : (term103 A s a) = (term104 A s a).
Proof. exact (MK_COMB (@lem3267465 A s a) (@lem3267460 A s a)). Qed.
Lemma lem3267467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267468 {A : Type'} (s : A -> Prop) (a : A) : (term105 A s a) = (term106 A s a).
Proof. exact (MK_COMB (@lem3267467) (@lem3267466 A s a)). Qed.
Lemma lem3267469 {A : Type'} (s : A -> Prop) (a : A) : (term107 A s a) = (term108 A s a).
Proof. exact (MK_COMB (@lem3267468 A s a) (@lem3267463 A s a)). Qed.
Lemma lem3267470 {A : Type'} (s : A -> Prop) (a : A) : (term109 A s a) = (term107 A s a).
Proof. exact (@lem17646 (term50 A s a) (term52 A s a)). Qed.
Lemma lem3267471 {A : Type'} (s : A -> Prop) (a : A) : (term109 A s a) = (term108 A s a).
Proof. exact (TRANS (@lem3267470 A s a) (@lem3267469 A s a)). Qed.
Lemma lem3267472 {A : Type'} (P : A -> Prop) : (term85 A P) = (term86 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3267473 {A : Type'} (s : A -> Prop) : (term110 A s) = (term111 A s).
Proof. exact (@lem3267472 A (term53 A s)). Qed.
Lemma lem3267474 {A : Type'} (s : A -> Prop) (a : A) : (term112 A s a) = ((term50 A s a) = (term52 A s a)).
Proof. exact (eq_refl (term112 A s a)). Qed.
Lemma lem3267475 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3267476 {A : Type'} (s : A -> Prop) (a : A) : (term113 A s a) = (term109 A s a).
Proof. exact (MK_COMB (@lem3267475) (@lem3267474 A s a)). Qed.
Lemma lem3267477 {A : Type'} (s : A -> Prop) (a : A) : (term113 A s a) = (term108 A s a).
Proof. exact (TRANS (@lem3267476 A s a) (@lem3267471 A s a)). Qed.
Lemma lem3267478 {A : Type'} (s : A -> Prop) : (term114 A s) = (term115 A s).
Proof. exact (fun_ext (fun a : A => @lem3267477 A s a)). Qed.
Lemma lem3267479 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267480 {A : Type'} (s : A -> Prop) : (term111 A s) = (term116 A s).
Proof. exact (MK_COMB (@lem3267479 A) (@lem3267478 A s)). Qed.
Lemma lem3267481 {A : Type'} (s : A -> Prop) : (term110 A s) = (term116 A s).
Proof. exact (TRANS (@lem3267473 A s) (@lem3267480 A s)). Qed.
Lemma lem3267482 {A : Type'} (P : type686 A) : (term117 A P) = (term118 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3267483 {A : Type'} : (term119 A) = (term120 A).
Proof. exact (@lem3267482 A (term55 A)). Qed.
Lemma lem3267484 {A : Type'} (s : A -> Prop) : (term121 A s) = (term54 A s).
Proof. exact (eq_refl (term121 A s)). Qed.
Lemma lem3267485 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3267486 {A : Type'} (s : A -> Prop) : (term122 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem3267485) (@lem3267484 A s)). Qed.
Lemma lem3267487 {A : Type'} (s : A -> Prop) : (term122 A s) = (term116 A s).
Proof. exact (TRANS (@lem3267486 A s) (@lem3267481 A s)). Qed.
Lemma lem3267488 {A : Type'} : (term123 A) = (term124 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267487 A s)). Qed.
Lemma lem3267489 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3267490 {A : Type'} : (term120 A) = (term125 A).
Proof. exact (MK_COMB (@lem3267489 A) (@lem3267488 A)). Qed.
Lemma lem3267491 {A : Type'} : (term119 A) = (term125 A).
Proof. exact (TRANS (@lem3267483 A) (@lem3267490 A)). Qed.
Lemma lem3267500 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term65 A a s x) = (term126 A a s x).
Proof. exact (@lem17045 (x = a) (s x)). Qed.
Lemma lem3267505 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term127 A a s x) = (term62 A a s x).
Proof. exact (@lem16933 (term62 A a s x)). Qed.
Lemma lem3267506 {A : Type'} (P : A -> Prop) : (term85 A P) = (term86 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3267507 {A : Type'} (a : A) (s : A -> Prop) : (term128 A a s) = (term129 A a s).
Proof. exact (@lem3267506 A (term67 A a s)). Qed.
Lemma lem3267508 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term130 A a s x) = (term65 A a s x).
Proof. exact (eq_refl (term130 A a s x)). Qed.
Lemma lem3267509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3267510 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term131 A a s x) = (term127 A a s x).
Proof. exact (MK_COMB (@lem3267509) (@lem3267508 A a s x)). Qed.
Lemma lem3267511 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term131 A a s x) = (term62 A a s x).
Proof. exact (TRANS (@lem3267510 A a s x) (@lem3267505 A a s x)). Qed.
Lemma lem3267512 {A : Type'} (a : A) (s : A -> Prop) : (term132 A a s) = (term133 A a s).
Proof. exact (fun_ext (fun x : A => @lem3267511 A a s x)). Qed.
Lemma lem3267513 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267514 {A : Type'} (a : A) (s : A -> Prop) : (term129 A a s) = (term134 A a s).
Proof. exact (MK_COMB (@lem3267513 A) (@lem3267512 A a s)). Qed.
Lemma lem3267515 {A : Type'} (a : A) (s : A -> Prop) : (term128 A a s) = (term134 A a s).
Proof. exact (TRANS (@lem3267507 A a s) (@lem3267514 A a s)). Qed.
Lemma lem3267516 {A : Type'} (a : A) (s : A -> Prop) : (term67 A a s) = (term135 A a s).
Proof. exact (fun_ext (fun x : A => @lem3267500 A a s x)). Qed.
Lemma lem3267517 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3267518 {A : Type'} (a : A) (s : A -> Prop) : (term68 A a s) = (term136 A a s).
Proof. exact (MK_COMB (@lem3267517 A) (@lem3267516 A a s)). Qed.
Lemma lem3267519 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term52 A s a).
Proof. exact (eq_refl (term52 A s a)). Qed.
Lemma lem3267522 {A : Type'} (s : A -> Prop) (a : A) : (term96 A s a) = (s a).
Proof. exact (@lem16933 (s a)). Qed.
Lemma lem3267523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3267524 {A : Type'} (a : A) (s : A -> Prop) : (term137 A a s) = (term138 A a s).
Proof. exact (MK_COMB (@lem3267523) (@lem3267515 A a s)). Qed.
Lemma lem3267525 {A : Type'} (s : A -> Prop) (a : A) : (term139 A s a) = (term140 A s a).
Proof. exact (MK_COMB (@lem3267524 A a s) (@lem3267519 A s a)). Qed.
Lemma lem3267526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3267527 {A : Type'} (a : A) (s : A -> Prop) : (term141 A a s) = (term142 A a s).
Proof. exact (MK_COMB (@lem3267526) (@lem3267518 A a s)). Qed.
Lemma lem3267528 {A : Type'} (s : A -> Prop) (a : A) : (term143 A s a) = (term144 A s a).
Proof. exact (MK_COMB (@lem3267527 A a s) (@lem3267522 A s a)). Qed.
Lemma lem3267529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267530 {A : Type'} (s : A -> Prop) (a : A) : (term145 A s a) = (term146 A s a).
Proof. exact (MK_COMB (@lem3267529) (@lem3267528 A s a)). Qed.
Lemma lem3267531 {A : Type'} (s : A -> Prop) (a : A) : (term147 A s a) = (term148 A s a).
Proof. exact (MK_COMB (@lem3267530 A s a) (@lem3267525 A s a)). Qed.
Lemma lem3267532 {A : Type'} (s : A -> Prop) (a : A) : (term149 A s a) = (term147 A s a).
Proof. exact (@lem17646 (term68 A a s) (term52 A s a)). Qed.
Lemma lem3267533 {A : Type'} (s : A -> Prop) (a : A) : (term149 A s a) = (term148 A s a).
Proof. exact (TRANS (@lem3267532 A s a) (@lem3267531 A s a)). Qed.
Lemma lem3267534 {A : Type'} (P : A -> Prop) : (term85 A P) = (term86 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3267535 {A : Type'} (s : A -> Prop) : (term150 A s) = (term151 A s).
Proof. exact (@lem3267534 A (term70 A s)). Qed.
Lemma lem3267536 {A : Type'} (s : A -> Prop) (a : A) : (term152 A s a) = ((term68 A a s) = (term52 A s a)).
Proof. exact (eq_refl (term152 A s a)). Qed.
Lemma lem3267537 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3267538 {A : Type'} (s : A -> Prop) (a : A) : (term153 A s a) = (term149 A s a).
Proof. exact (MK_COMB (@lem3267537) (@lem3267536 A s a)). Qed.
Lemma lem3267539 {A : Type'} (s : A -> Prop) (a : A) : (term153 A s a) = (term148 A s a).
Proof. exact (TRANS (@lem3267538 A s a) (@lem3267533 A s a)). Qed.
Lemma lem3267540 {A : Type'} (s : A -> Prop) : (term154 A s) = (term155 A s).
Proof. exact (fun_ext (fun a : A => @lem3267539 A s a)). Qed.
Lemma lem3267541 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267542 {A : Type'} (s : A -> Prop) : (term151 A s) = (term156 A s).
Proof. exact (MK_COMB (@lem3267541 A) (@lem3267540 A s)). Qed.
Lemma lem3267543 {A : Type'} (s : A -> Prop) : (term150 A s) = (term156 A s).
Proof. exact (TRANS (@lem3267535 A s) (@lem3267542 A s)). Qed.
Lemma lem3267544 {A : Type'} (P : type686 A) : (term117 A P) = (term118 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3267545 {A : Type'} : (term157 A) = (term158 A).
Proof. exact (@lem3267544 A (term72 A)). Qed.
Lemma lem3267546 {A : Type'} (s : A -> Prop) : (term159 A s) = (term71 A s).
Proof. exact (eq_refl (term159 A s)). Qed.
Lemma lem3267547 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3267548 {A : Type'} (s : A -> Prop) : (term160 A s) = (term150 A s).
Proof. exact (MK_COMB (@lem3267547) (@lem3267546 A s)). Qed.
Lemma lem3267549 {A : Type'} (s : A -> Prop) : (term160 A s) = (term156 A s).
Proof. exact (TRANS (@lem3267548 A s) (@lem3267543 A s)). Qed.
Lemma lem3267550 {A : Type'} : (term161 A) = (term162 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267549 A s)). Qed.
Lemma lem3267551 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3267552 {A : Type'} : (term158 A) = (term163 A).
Proof. exact (MK_COMB (@lem3267551 A) (@lem3267550 A)). Qed.
Lemma lem3267553 {A : Type'} : (term157 A) = (term163 A).
Proof. exact (TRANS (@lem3267545 A) (@lem3267552 A)). Qed.
Lemma lem3267554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267555 {A : Type'} : (term164 A) = (term165 A).
Proof. exact (MK_COMB (@lem3267554) (@lem3267491 A)). Qed.
Lemma lem3267556 {A : Type'} : (term166 A) = (term167 A).
Proof. exact (MK_COMB (@lem3267555 A) (@lem3267553 A)). Qed.
Lemma lem3267557 {A : Type'} : (term77 A) = (term166 A).
Proof. exact (@lem17045 (term56 A) (term73 A)). Qed.
Lemma lem3267558 {A : Type'} : (term77 A) = (term167 A).
Proof. exact (TRANS (@lem3267557 A) (@lem3267556 A)). Qed.
Lemma lem3267564 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3267565 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (@lem3267564 A P Q). Qed.
Lemma lem3267566 {A : Type'} (s : A -> Prop) : (term170 A s) = (term171 A s).
Proof. exact (@lem3267565 A (term172 A s) (term173 A s)). Qed.
Lemma lem3267567 {A : Type'} (s : A -> Prop) (a : A) : (term174 A s a) = (term104 A s a).
Proof. exact (eq_refl (term174 A s a)). Qed.
Lemma lem3267568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267569 {A : Type'} (s : A -> Prop) (a : A) : (term175 A s a) = (term106 A s a).
Proof. exact (MK_COMB (@lem3267568) (@lem3267567 A s a)). Qed.
Lemma lem3267570 {A : Type'} (s : A -> Prop) (a : A) : (term176 A s a) = (term100 A s a).
Proof. exact (eq_refl (term176 A s a)). Qed.
Lemma lem3267571 {A : Type'} (s : A -> Prop) (a : A) : (term177 A s a) = (term108 A s a).
Proof. exact (MK_COMB (@lem3267569 A s a) (@lem3267570 A s a)). Qed.
Lemma lem3267572 {A : Type'} (s : A -> Prop) : (term178 A s) = (term115 A s).
Proof. exact (fun_ext (fun a : A => @lem3267571 A s a)). Qed.
Lemma lem3267573 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267574 {A : Type'} (s : A -> Prop) : (term170 A s) = (term116 A s).
Proof. exact (MK_COMB (@lem3267573 A) (@lem3267572 A s)). Qed.
Lemma lem3267575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267576 {A : Type'} (s : A -> Prop) : (term179 A s) = (term180 A s).
Proof. exact (MK_COMB (@lem3267575) (@lem3267574 A s)). Qed.
Lemma lem3267577 {A : Type'} (s : A -> Prop) (a : A) : (term174 A s a) = (term104 A s a).
Proof. exact (eq_refl (term174 A s a)). Qed.
Lemma lem3267578 {A : Type'} (s : A -> Prop) : (term181 A s) = (term172 A s).
Proof. exact (fun_ext (fun a : A => @lem3267577 A s a)). Qed.
Lemma lem3267579 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267580 {A : Type'} (s : A -> Prop) : (term182 A s) = (term183 A s).
Proof. exact (MK_COMB (@lem3267579 A) (@lem3267578 A s)). Qed.
Lemma lem3267581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267582 {A : Type'} (s : A -> Prop) : (term184 A s) = (term185 A s).
Proof. exact (MK_COMB (@lem3267581) (@lem3267580 A s)). Qed.
Lemma lem3267583 {A : Type'} (s : A -> Prop) (a : A) : (term176 A s a) = (term100 A s a).
Proof. exact (eq_refl (term176 A s a)). Qed.
Lemma lem3267584 {A : Type'} (s : A -> Prop) : (term186 A s) = (term173 A s).
Proof. exact (fun_ext (fun a : A => @lem3267583 A s a)). Qed.
Lemma lem3267585 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267586 {A : Type'} (s : A -> Prop) : (term187 A s) = (term188 A s).
Proof. exact (MK_COMB (@lem3267585 A) (@lem3267584 A s)). Qed.
Lemma lem3267587 {A : Type'} (s : A -> Prop) : (term171 A s) = (term189 A s).
Proof. exact (MK_COMB (@lem3267582 A s) (@lem3267586 A s)). Qed.
Lemma lem3267588 {A : Type'} (s : A -> Prop) : ((term170 A s) = (term171 A s)) = ((term116 A s) = (term189 A s)).
Proof. exact (MK_COMB (@lem3267576 A s) (@lem3267587 A s)). Qed.
Lemma lem3267589 {A : Type'} (s : A -> Prop) : (term116 A s) = (term189 A s).
Proof. exact (EQ_MP (@lem3267588 A s) (@lem3267566 A s)). Qed.
Lemma lem3267746 {A : Type'} : (term124 A) = (term190 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267589 A s)). Qed.
Lemma lem3267747 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3267748 {A : Type'} : (term125 A) = (term191 A).
Proof. exact (MK_COMB (@lem3267747 A) (@lem3267746 A)). Qed.
Lemma lem3267750 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3267751 {A : Type'} (P : type686 A) (Q : type686 A) : (term192 A P Q) = (term193 A P Q).
Proof. exact (@lem3267750 (A -> Prop) P Q). Qed.
Lemma lem3267752 {A : Type'} : (term194 A) = (term195 A).
Proof. exact (@lem3267751 A (term196 A) (term197 A)). Qed.
Lemma lem3267753 {A : Type'} (s : A -> Prop) : (term198 A s) = (term183 A s).
Proof. exact (eq_refl (term198 A s)). Qed.
Lemma lem3267754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267755 {A : Type'} (s : A -> Prop) : (term199 A s) = (term185 A s).
Proof. exact (MK_COMB (@lem3267754) (@lem3267753 A s)). Qed.
Lemma lem3267756 {A : Type'} (s : A -> Prop) : (term200 A s) = (term188 A s).
Proof. exact (eq_refl (term200 A s)). Qed.
Lemma lem3267757 {A : Type'} (s : A -> Prop) : (term201 A s) = (term189 A s).
Proof. exact (MK_COMB (@lem3267755 A s) (@lem3267756 A s)). Qed.
Lemma lem3267758 {A : Type'} : (term202 A) = (term190 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267757 A s)). Qed.
Lemma lem3267759 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3267760 {A : Type'} : (term194 A) = (term191 A).
Proof. exact (MK_COMB (@lem3267759 A) (@lem3267758 A)). Qed.
Lemma lem3267761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267762 {A : Type'} : (term203 A) = (term204 A).
Proof. exact (MK_COMB (@lem3267761) (@lem3267760 A)). Qed.
Lemma lem3267763 {A : Type'} (s : A -> Prop) : (term198 A s) = (term183 A s).
Proof. exact (eq_refl (term198 A s)). Qed.
Lemma lem3267764 {A : Type'} : (term205 A) = (term196 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267763 A s)). Qed.
Lemma lem3267765 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3267766 {A : Type'} : (term206 A) = (term207 A).
Proof. exact (MK_COMB (@lem3267765 A) (@lem3267764 A)). Qed.
Lemma lem3267767 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267768 {A : Type'} : (term208 A) = (term209 A).
Proof. exact (MK_COMB (@lem3267767) (@lem3267766 A)). Qed.
Lemma lem3267769 {A : Type'} (s : A -> Prop) : (term200 A s) = (term188 A s).
Proof. exact (eq_refl (term200 A s)). Qed.
Lemma lem3267770 {A : Type'} : (term210 A) = (term197 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267769 A s)). Qed.
Lemma lem3267771 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3267772 {A : Type'} : (term211 A) = (term212 A).
Proof. exact (MK_COMB (@lem3267771 A) (@lem3267770 A)). Qed.
Lemma lem3267773 {A : Type'} : (term195 A) = (term213 A).
Proof. exact (MK_COMB (@lem3267768 A) (@lem3267772 A)). Qed.
Lemma lem3267774 {A : Type'} : ((term194 A) = (term195 A)) = ((term191 A) = (term213 A)).
Proof. exact (MK_COMB (@lem3267762 A) (@lem3267773 A)). Qed.
Lemma lem3267775 {A : Type'} : (term191 A) = (term213 A).
Proof. exact (EQ_MP (@lem3267774 A) (@lem3267752 A)). Qed.
Lemma lem3267940 {A : Type'} : (term125 A) = (term213 A).
Proof. exact (TRANS (@lem3267748 A) (@lem3267775 A)). Qed.
Lemma lem3267941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267942 {A : Type'} : (term165 A) = (term214 A).
Proof. exact (MK_COMB (@lem3267941) (@lem3267940 A)). Qed.
Lemma lem3267948 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3267949 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (@lem3267948 A P Q). Qed.
Lemma lem3267950 {A : Type'} (s : A -> Prop) : (term215 A s) = (term216 A s).
Proof. exact (@lem3267949 A (term217 A s) (term218 A s)). Qed.
Lemma lem3267951 {A : Type'} (s : A -> Prop) (a : A) : (term219 A s a) = (term144 A s a).
Proof. exact (eq_refl (term219 A s a)). Qed.
Lemma lem3267952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267953 {A : Type'} (s : A -> Prop) (a : A) : (term220 A s a) = (term146 A s a).
Proof. exact (MK_COMB (@lem3267952) (@lem3267951 A s a)). Qed.
Lemma lem3267954 {A : Type'} (s : A -> Prop) (a : A) : (term221 A s a) = (term140 A s a).
Proof. exact (eq_refl (term221 A s a)). Qed.
Lemma lem3267955 {A : Type'} (s : A -> Prop) (a : A) : (term222 A s a) = (term148 A s a).
Proof. exact (MK_COMB (@lem3267953 A s a) (@lem3267954 A s a)). Qed.
Lemma lem3267956 {A : Type'} (s : A -> Prop) : (term223 A s) = (term155 A s).
Proof. exact (fun_ext (fun a : A => @lem3267955 A s a)). Qed.
Lemma lem3267957 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267958 {A : Type'} (s : A -> Prop) : (term215 A s) = (term156 A s).
Proof. exact (MK_COMB (@lem3267957 A) (@lem3267956 A s)). Qed.
Lemma lem3267959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3267960 {A : Type'} (s : A -> Prop) : (term224 A s) = (term225 A s).
Proof. exact (MK_COMB (@lem3267959) (@lem3267958 A s)). Qed.
Lemma lem3267961 {A : Type'} (s : A -> Prop) (a : A) : (term219 A s a) = (term144 A s a).
Proof. exact (eq_refl (term219 A s a)). Qed.
Lemma lem3267962 {A : Type'} (s : A -> Prop) : (term226 A s) = (term217 A s).
Proof. exact (fun_ext (fun a : A => @lem3267961 A s a)). Qed.
Lemma lem3267963 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267964 {A : Type'} (s : A -> Prop) : (term227 A s) = (term228 A s).
Proof. exact (MK_COMB (@lem3267963 A) (@lem3267962 A s)). Qed.
Lemma lem3267965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3267966 {A : Type'} (s : A -> Prop) : (term229 A s) = (term230 A s).
Proof. exact (MK_COMB (@lem3267965) (@lem3267964 A s)). Qed.
Lemma lem3267967 {A : Type'} (s : A -> Prop) (a : A) : (term221 A s a) = (term140 A s a).
Proof. exact (eq_refl (term221 A s a)). Qed.
Lemma lem3267968 {A : Type'} (s : A -> Prop) : (term231 A s) = (term218 A s).
Proof. exact (fun_ext (fun a : A => @lem3267967 A s a)). Qed.
Lemma lem3267969 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3267970 {A : Type'} (s : A -> Prop) : (term232 A s) = (term233 A s).
Proof. exact (MK_COMB (@lem3267969 A) (@lem3267968 A s)). Qed.
Lemma lem3267971 {A : Type'} (s : A -> Prop) : (term216 A s) = (term234 A s).
Proof. exact (MK_COMB (@lem3267966 A s) (@lem3267970 A s)). Qed.
Lemma lem3267972 {A : Type'} (s : A -> Prop) : ((term215 A s) = (term216 A s)) = ((term156 A s) = (term234 A s)).
Proof. exact (MK_COMB (@lem3267960 A s) (@lem3267971 A s)). Qed.
Lemma lem3267973 {A : Type'} (s : A -> Prop) : (term156 A s) = (term234 A s).
Proof. exact (EQ_MP (@lem3267972 A s) (@lem3267950 A s)). Qed.
Lemma lem3268134 {A : Type'} : (term162 A) = (term235 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3267973 A s)). Qed.
Lemma lem3268135 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268136 {A : Type'} : (term163 A) = (term236 A).
Proof. exact (MK_COMB (@lem3268135 A) (@lem3268134 A)). Qed.
Lemma lem3268138 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3268139 {A : Type'} (P : type686 A) (Q : type686 A) : (term192 A P Q) = (term193 A P Q).
Proof. exact (@lem3268138 (A -> Prop) P Q). Qed.
Lemma lem3268140 {A : Type'} : (term237 A) = (term238 A).
Proof. exact (@lem3268139 A (term239 A) (term240 A)). Qed.
Lemma lem3268141 {A : Type'} (s : A -> Prop) : (term241 A s) = (term228 A s).
Proof. exact (eq_refl (term241 A s)). Qed.
Lemma lem3268142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268143 {A : Type'} (s : A -> Prop) : (term242 A s) = (term230 A s).
Proof. exact (MK_COMB (@lem3268142) (@lem3268141 A s)). Qed.
Lemma lem3268144 {A : Type'} (s : A -> Prop) : (term243 A s) = (term233 A s).
Proof. exact (eq_refl (term243 A s)). Qed.
Lemma lem3268145 {A : Type'} (s : A -> Prop) : (term244 A s) = (term234 A s).
Proof. exact (MK_COMB (@lem3268143 A s) (@lem3268144 A s)). Qed.
Lemma lem3268146 {A : Type'} : (term245 A) = (term235 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268145 A s)). Qed.
Lemma lem3268147 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268148 {A : Type'} : (term237 A) = (term236 A).
Proof. exact (MK_COMB (@lem3268147 A) (@lem3268146 A)). Qed.
Lemma lem3268149 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268150 {A : Type'} : (term246 A) = (term247 A).
Proof. exact (MK_COMB (@lem3268149) (@lem3268148 A)). Qed.
Lemma lem3268151 {A : Type'} (s : A -> Prop) : (term241 A s) = (term228 A s).
Proof. exact (eq_refl (term241 A s)). Qed.
Lemma lem3268152 {A : Type'} : (term248 A) = (term239 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268151 A s)). Qed.
Lemma lem3268153 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268154 {A : Type'} : (term249 A) = (term250 A).
Proof. exact (MK_COMB (@lem3268153 A) (@lem3268152 A)). Qed.
Lemma lem3268155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268156 {A : Type'} : (term251 A) = (term252 A).
Proof. exact (MK_COMB (@lem3268155) (@lem3268154 A)). Qed.
Lemma lem3268157 {A : Type'} (s : A -> Prop) : (term243 A s) = (term233 A s).
Proof. exact (eq_refl (term243 A s)). Qed.
Lemma lem3268158 {A : Type'} : (term253 A) = (term240 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268157 A s)). Qed.
Lemma lem3268159 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268160 {A : Type'} : (term254 A) = (term255 A).
Proof. exact (MK_COMB (@lem3268159 A) (@lem3268158 A)). Qed.
Lemma lem3268161 {A : Type'} : (term238 A) = (term256 A).
Proof. exact (MK_COMB (@lem3268156 A) (@lem3268160 A)). Qed.
Lemma lem3268162 {A : Type'} : ((term237 A) = (term238 A)) = ((term236 A) = (term256 A)).
Proof. exact (MK_COMB (@lem3268150 A) (@lem3268161 A)). Qed.
Lemma lem3268163 {A : Type'} : (term236 A) = (term256 A).
Proof. exact (EQ_MP (@lem3268162 A) (@lem3268140 A)). Qed.
Lemma lem3268332 {A : Type'} : (term163 A) = (term256 A).
Proof. exact (TRANS (@lem3268136 A) (@lem3268163 A)). Qed.
Lemma lem3268333 {A : Type'} : (term167 A) = (term257 A).
Proof. exact (MK_COMB (@lem3267942 A) (@lem3268332 A)). Qed.
Lemma lem3268335 {A : Type'} (P : A -> Prop) (Q : Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3268336 {A : Type'} (P : A -> Prop) (Q : Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (@lem3268335 A P Q). Qed.
Lemma lem3268337 {A : Type'} (s : A -> Prop) (a : A) : (term260 A s a) = (term261 A s a).
Proof. exact (@lem3268336 A (term92 A s a) (term52 A s a)). Qed.
Lemma lem3268338 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term262 A s a x) = (term44 A s x a).
Proof. exact (eq_refl (term262 A s a x)). Qed.
Lemma lem3268339 {A : Type'} (s : A -> Prop) (a : A) : (term263 A s a) = (term92 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268338 A s x a)). Qed.
Lemma lem3268340 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268341 {A : Type'} (s : A -> Prop) (a : A) : (term264 A s a) = (term93 A s a).
Proof. exact (MK_COMB (@lem3268340 A) (@lem3268339 A s a)). Qed.
Lemma lem3268342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3268343 {A : Type'} (s : A -> Prop) (a : A) : (term265 A s a) = (term98 A s a).
Proof. exact (MK_COMB (@lem3268342) (@lem3268341 A s a)). Qed.
Lemma lem3268344 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term52 A s a).
Proof. exact (eq_refl (term52 A s a)). Qed.
Lemma lem3268345 {A : Type'} (s : A -> Prop) (a : A) : (term260 A s a) = (term100 A s a).
Proof. exact (MK_COMB (@lem3268343 A s a) (@lem3268344 A s a)). Qed.
Lemma lem3268346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268347 {A : Type'} (s : A -> Prop) (a : A) : (term266 A s a) = (term267 A s a).
Proof. exact (MK_COMB (@lem3268346) (@lem3268345 A s a)). Qed.
Lemma lem3268348 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term262 A s a x) = (term44 A s x a).
Proof. exact (eq_refl (term262 A s a x)). Qed.
Lemma lem3268349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3268350 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term268 A s a x) = (term269 A s x a).
Proof. exact (MK_COMB (@lem3268349) (@lem3268348 A s x a)). Qed.
Lemma lem3268351 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term52 A s a).
Proof. exact (eq_refl (term52 A s a)). Qed.
Lemma lem3268352 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term270 A x s a) = (term271 A x s a).
Proof. exact (MK_COMB (@lem3268350 A s x a) (@lem3268351 A s a)). Qed.
Lemma lem3268353 {A : Type'} (s : A -> Prop) (a : A) : (term272 A s a) = (term273 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268352 A x s a)). Qed.
Lemma lem3268354 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268355 {A : Type'} (s : A -> Prop) (a : A) : (term261 A s a) = (term274 A s a).
Proof. exact (MK_COMB (@lem3268354 A) (@lem3268353 A s a)). Qed.
Lemma lem3268356 {A : Type'} (s : A -> Prop) (a : A) : ((term260 A s a) = (term261 A s a)) = ((term100 A s a) = (term274 A s a)).
Proof. exact (MK_COMB (@lem3268347 A s a) (@lem3268355 A s a)). Qed.
Lemma lem3268357 {A : Type'} (s : A -> Prop) (a : A) : (term100 A s a) = (term274 A s a).
Proof. exact (EQ_MP (@lem3268356 A s a) (@lem3268337 A s a)). Qed.
Lemma lem3268358 {A : Type'} (s : A -> Prop) : (term173 A s) = (term275 A s).
Proof. exact (fun_ext (fun a : A => @lem3268357 A s a)). Qed.
Lemma lem3268359 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268360 {A : Type'} (s : A -> Prop) : (term188 A s) = (term276 A s).
Proof. exact (MK_COMB (@lem3268359 A) (@lem3268358 A s)). Qed.
Lemma lem3268361 {A : Type'} : (term197 A) = (term277 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268360 A s)). Qed.
Lemma lem3268362 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268363 {A : Type'} : (term212 A) = (term278 A).
Proof. exact (MK_COMB (@lem3268362 A) (@lem3268361 A)). Qed.
Lemma lem3268364 {A : Type'} : (term209 A) = (term209 A).
Proof. exact (eq_refl (term209 A)). Qed.
Lemma lem3268365 {A : Type'} : (term213 A) = (term279 A).
Proof. exact (MK_COMB (@lem3268364 A) (@lem3268363 A)). Qed.
Lemma lem3268367 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3268368 {A : Type'} (P : type686 A) (Q : type686 A) : (term193 A P Q) = (term192 A P Q).
Proof. exact (@lem3268367 (A -> Prop) P Q). Qed.
Lemma lem3268369 {A : Type'} : (term280 A) = (term281 A).
Proof. exact (@lem3268368 A (term196 A) (term277 A)). Qed.
Lemma lem3268370 {A : Type'} (s : A -> Prop) : (term198 A s) = (term183 A s).
Proof. exact (eq_refl (term198 A s)). Qed.
Lemma lem3268371 {A : Type'} : (term205 A) = (term196 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268370 A s)). Qed.
Lemma lem3268372 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268373 {A : Type'} : (term206 A) = (term207 A).
Proof. exact (MK_COMB (@lem3268372 A) (@lem3268371 A)). Qed.
Lemma lem3268374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268375 {A : Type'} : (term208 A) = (term209 A).
Proof. exact (MK_COMB (@lem3268374) (@lem3268373 A)). Qed.
Lemma lem3268376 {A : Type'} (s : A -> Prop) : (term282 A s) = (term276 A s).
Proof. exact (eq_refl (term282 A s)). Qed.
Lemma lem3268377 {A : Type'} : (term283 A) = (term277 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268376 A s)). Qed.
Lemma lem3268378 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268379 {A : Type'} : (term284 A) = (term278 A).
Proof. exact (MK_COMB (@lem3268378 A) (@lem3268377 A)). Qed.
Lemma lem3268380 {A : Type'} : (term280 A) = (term279 A).
Proof. exact (MK_COMB (@lem3268375 A) (@lem3268379 A)). Qed.
Lemma lem3268381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268382 {A : Type'} : (term285 A) = (term286 A).
Proof. exact (MK_COMB (@lem3268381) (@lem3268380 A)). Qed.
Lemma lem3268383 {A : Type'} (s : A -> Prop) : (term198 A s) = (term183 A s).
Proof. exact (eq_refl (term198 A s)). Qed.
Lemma lem3268384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268385 {A : Type'} (s : A -> Prop) : (term199 A s) = (term185 A s).
Proof. exact (MK_COMB (@lem3268384) (@lem3268383 A s)). Qed.
Lemma lem3268386 {A : Type'} (s : A -> Prop) : (term282 A s) = (term276 A s).
Proof. exact (eq_refl (term282 A s)). Qed.
Lemma lem3268387 {A : Type'} (s : A -> Prop) : (term287 A s) = (term288 A s).
Proof. exact (MK_COMB (@lem3268385 A s) (@lem3268386 A s)). Qed.
Lemma lem3268388 {A : Type'} : (term289 A) = (term290 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268387 A s)). Qed.
Lemma lem3268389 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268390 {A : Type'} : (term281 A) = (term291 A).
Proof. exact (MK_COMB (@lem3268389 A) (@lem3268388 A)). Qed.
Lemma lem3268391 {A : Type'} : ((term280 A) = (term281 A)) = ((term279 A) = (term291 A)).
Proof. exact (MK_COMB (@lem3268382 A) (@lem3268390 A)). Qed.
Lemma lem3268392 {A : Type'} : (term279 A) = (term291 A).
Proof. exact (EQ_MP (@lem3268391 A) (@lem3268369 A)). Qed.
Lemma lem3268394 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3268395 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (@lem3268394 A P Q). Qed.
Lemma lem3268396 {A : Type'} (s : A -> Prop) : (term292 A s) = (term293 A s).
Proof. exact (@lem3268395 A (term172 A s) (term275 A s)). Qed.
Lemma lem3268397 {A : Type'} (s : A -> Prop) (a : A) : (term174 A s a) = (term104 A s a).
Proof. exact (eq_refl (term174 A s a)). Qed.
Lemma lem3268398 {A : Type'} (s : A -> Prop) : (term181 A s) = (term172 A s).
Proof. exact (fun_ext (fun a : A => @lem3268397 A s a)). Qed.
Lemma lem3268399 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268400 {A : Type'} (s : A -> Prop) : (term182 A s) = (term183 A s).
Proof. exact (MK_COMB (@lem3268399 A) (@lem3268398 A s)). Qed.
Lemma lem3268401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268402 {A : Type'} (s : A -> Prop) : (term184 A s) = (term185 A s).
Proof. exact (MK_COMB (@lem3268401) (@lem3268400 A s)). Qed.
Lemma lem3268403 {A : Type'} (s : A -> Prop) (a : A) : (term294 A s a) = (term274 A s a).
Proof. exact (eq_refl (term294 A s a)). Qed.
Lemma lem3268404 {A : Type'} (s : A -> Prop) : (term295 A s) = (term275 A s).
Proof. exact (fun_ext (fun a : A => @lem3268403 A s a)). Qed.
Lemma lem3268405 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268406 {A : Type'} (s : A -> Prop) : (term296 A s) = (term276 A s).
Proof. exact (MK_COMB (@lem3268405 A) (@lem3268404 A s)). Qed.
Lemma lem3268407 {A : Type'} (s : A -> Prop) : (term292 A s) = (term288 A s).
Proof. exact (MK_COMB (@lem3268402 A s) (@lem3268406 A s)). Qed.
Lemma lem3268408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268409 {A : Type'} (s : A -> Prop) : (term297 A s) = (term298 A s).
Proof. exact (MK_COMB (@lem3268408) (@lem3268407 A s)). Qed.
Lemma lem3268410 {A : Type'} (s : A -> Prop) (a : A) : (term174 A s a) = (term104 A s a).
Proof. exact (eq_refl (term174 A s a)). Qed.
Lemma lem3268411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268412 {A : Type'} (s : A -> Prop) (a : A) : (term175 A s a) = (term106 A s a).
Proof. exact (MK_COMB (@lem3268411) (@lem3268410 A s a)). Qed.
Lemma lem3268413 {A : Type'} (s : A -> Prop) (a : A) : (term294 A s a) = (term274 A s a).
Proof. exact (eq_refl (term294 A s a)). Qed.
Lemma lem3268414 {A : Type'} (s : A -> Prop) (a : A) : (term299 A s a) = (term300 A s a).
Proof. exact (MK_COMB (@lem3268412 A s a) (@lem3268413 A s a)). Qed.
Lemma lem3268415 {A : Type'} (s : A -> Prop) : (term301 A s) = (term302 A s).
Proof. exact (fun_ext (fun a : A => @lem3268414 A s a)). Qed.
Lemma lem3268416 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268417 {A : Type'} (s : A -> Prop) : (term293 A s) = (term303 A s).
Proof. exact (MK_COMB (@lem3268416 A) (@lem3268415 A s)). Qed.
Lemma lem3268418 {A : Type'} (s : A -> Prop) : ((term292 A s) = (term293 A s)) = ((term288 A s) = (term303 A s)).
Proof. exact (MK_COMB (@lem3268409 A s) (@lem3268417 A s)). Qed.
Lemma lem3268419 {A : Type'} (s : A -> Prop) : (term288 A s) = (term303 A s).
Proof. exact (EQ_MP (@lem3268418 A s) (@lem3268396 A s)). Qed.
Lemma lem3268421 {A : Type'} (P : Prop) (Q : A -> Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3268422 {A : Type'} (P : Prop) (Q : A -> Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (@lem3268421 A P Q). Qed.
Lemma lem3268423 {A : Type'} (s : A -> Prop) (a : A) : (term306 A s a) = (term307 A s a).
Proof. exact (@lem3268422 A (term104 A s a) (term273 A s a)). Qed.
Lemma lem3268424 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term308 A s a x) = (term271 A x s a).
Proof. exact (eq_refl (term308 A s a x)). Qed.
Lemma lem3268425 {A : Type'} (s : A -> Prop) (a : A) : (term309 A s a) = (term273 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268424 A x s a)). Qed.
Lemma lem3268426 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268427 {A : Type'} (s : A -> Prop) (a : A) : (term310 A s a) = (term274 A s a).
Proof. exact (MK_COMB (@lem3268426 A) (@lem3268425 A s a)). Qed.
Lemma lem3268428 {A : Type'} (s : A -> Prop) (a : A) : (term106 A s a) = (term106 A s a).
Proof. exact (eq_refl (term106 A s a)). Qed.
Lemma lem3268429 {A : Type'} (s : A -> Prop) (a : A) : (term306 A s a) = (term300 A s a).
Proof. exact (MK_COMB (@lem3268428 A s a) (@lem3268427 A s a)). Qed.
Lemma lem3268430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268431 {A : Type'} (s : A -> Prop) (a : A) : (term311 A s a) = (term312 A s a).
Proof. exact (MK_COMB (@lem3268430) (@lem3268429 A s a)). Qed.
Lemma lem3268432 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term308 A s a x) = (term271 A x s a).
Proof. exact (eq_refl (term308 A s a x)). Qed.
Lemma lem3268433 {A : Type'} (s : A -> Prop) (a : A) : (term106 A s a) = (term106 A s a).
Proof. exact (eq_refl (term106 A s a)). Qed.
Lemma lem3268434 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term313 A s a x) = (term314 A x s a).
Proof. exact (MK_COMB (@lem3268433 A s a) (@lem3268432 A x s a)). Qed.
Lemma lem3268435 {A : Type'} (s : A -> Prop) (a : A) : (term315 A s a) = (term316 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268434 A x s a)). Qed.
Lemma lem3268436 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268437 {A : Type'} (s : A -> Prop) (a : A) : (term307 A s a) = (term317 A s a).
Proof. exact (MK_COMB (@lem3268436 A) (@lem3268435 A s a)). Qed.
Lemma lem3268438 {A : Type'} (s : A -> Prop) (a : A) : ((term306 A s a) = (term307 A s a)) = ((term300 A s a) = (term317 A s a)).
Proof. exact (MK_COMB (@lem3268431 A s a) (@lem3268437 A s a)). Qed.
Lemma lem3268439 {A : Type'} (s : A -> Prop) (a : A) : (term300 A s a) = (term317 A s a).
Proof. exact (EQ_MP (@lem3268438 A s a) (@lem3268423 A s a)). Qed.
Lemma lem3268440 {A : Type'} (s : A -> Prop) : (term302 A s) = (term318 A s).
Proof. exact (fun_ext (fun a : A => @lem3268439 A s a)). Qed.
Lemma lem3268441 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268442 {A : Type'} (s : A -> Prop) : (term303 A s) = (term319 A s).
Proof. exact (MK_COMB (@lem3268441 A) (@lem3268440 A s)). Qed.
Lemma lem3268443 {A : Type'} (s : A -> Prop) : (term288 A s) = (term319 A s).
Proof. exact (TRANS (@lem3268419 A s) (@lem3268442 A s)). Qed.
Lemma lem3268444 {A : Type'} : (term290 A) = (term320 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268443 A s)). Qed.
Lemma lem3268445 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268446 {A : Type'} : (term291 A) = (term321 A).
Proof. exact (MK_COMB (@lem3268445 A) (@lem3268444 A)). Qed.
Lemma lem3268447 {A : Type'} : (term279 A) = (term321 A).
Proof. exact (TRANS (@lem3268392 A) (@lem3268446 A)). Qed.
Lemma lem3268448 {A : Type'} : (term213 A) = (term321 A).
Proof. exact (TRANS (@lem3268365 A) (@lem3268447 A)). Qed.
Lemma lem3268449 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268450 {A : Type'} : (term214 A) = (term322 A).
Proof. exact (MK_COMB (@lem3268449) (@lem3268448 A)). Qed.
Lemma lem3268452 {A : Type'} (P : A -> Prop) (Q : Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3268453 {A : Type'} (P : A -> Prop) (Q : Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (@lem3268452 A P Q). Qed.
Lemma lem3268454 {A : Type'} (s : A -> Prop) (a : A) : (term323 A s a) = (term324 A s a).
Proof. exact (@lem3268453 A (term133 A a s) (term52 A s a)). Qed.
Lemma lem3268455 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term325 A a s x) = (term62 A a s x).
Proof. exact (eq_refl (term325 A a s x)). Qed.
Lemma lem3268456 {A : Type'} (a : A) (s : A -> Prop) : (term326 A a s) = (term133 A a s).
Proof. exact (fun_ext (fun x : A => @lem3268455 A a s x)). Qed.
Lemma lem3268457 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268458 {A : Type'} (a : A) (s : A -> Prop) : (term327 A a s) = (term134 A a s).
Proof. exact (MK_COMB (@lem3268457 A) (@lem3268456 A a s)). Qed.
Lemma lem3268459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3268460 {A : Type'} (a : A) (s : A -> Prop) : (term328 A a s) = (term138 A a s).
Proof. exact (MK_COMB (@lem3268459) (@lem3268458 A a s)). Qed.
Lemma lem3268461 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term52 A s a).
Proof. exact (eq_refl (term52 A s a)). Qed.
Lemma lem3268462 {A : Type'} (s : A -> Prop) (a : A) : (term323 A s a) = (term140 A s a).
Proof. exact (MK_COMB (@lem3268460 A a s) (@lem3268461 A s a)). Qed.
Lemma lem3268463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268464 {A : Type'} (s : A -> Prop) (a : A) : (term329 A s a) = (term330 A s a).
Proof. exact (MK_COMB (@lem3268463) (@lem3268462 A s a)). Qed.
Lemma lem3268465 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term325 A a s x) = (term62 A a s x).
Proof. exact (eq_refl (term325 A a s x)). Qed.
Lemma lem3268466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3268467 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term331 A a s x) = (term332 A a s x).
Proof. exact (MK_COMB (@lem3268466) (@lem3268465 A a s x)). Qed.
Lemma lem3268468 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term52 A s a).
Proof. exact (eq_refl (term52 A s a)). Qed.
Lemma lem3268469 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term333 A x s a) = (term334 A x s a).
Proof. exact (MK_COMB (@lem3268467 A a s x) (@lem3268468 A s a)). Qed.
Lemma lem3268470 {A : Type'} (s : A -> Prop) (a : A) : (term335 A s a) = (term336 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268469 A x s a)). Qed.
Lemma lem3268471 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268472 {A : Type'} (s : A -> Prop) (a : A) : (term324 A s a) = (term337 A s a).
Proof. exact (MK_COMB (@lem3268471 A) (@lem3268470 A s a)). Qed.
Lemma lem3268473 {A : Type'} (s : A -> Prop) (a : A) : ((term323 A s a) = (term324 A s a)) = ((term140 A s a) = (term337 A s a)).
Proof. exact (MK_COMB (@lem3268464 A s a) (@lem3268472 A s a)). Qed.
Lemma lem3268474 {A : Type'} (s : A -> Prop) (a : A) : (term140 A s a) = (term337 A s a).
Proof. exact (EQ_MP (@lem3268473 A s a) (@lem3268454 A s a)). Qed.
Lemma lem3268475 {A : Type'} (s : A -> Prop) : (term218 A s) = (term338 A s).
Proof. exact (fun_ext (fun a : A => @lem3268474 A s a)). Qed.
Lemma lem3268476 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268477 {A : Type'} (s : A -> Prop) : (term233 A s) = (term339 A s).
Proof. exact (MK_COMB (@lem3268476 A) (@lem3268475 A s)). Qed.
Lemma lem3268478 {A : Type'} : (term240 A) = (term340 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268477 A s)). Qed.
Lemma lem3268479 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268480 {A : Type'} : (term255 A) = (term341 A).
Proof. exact (MK_COMB (@lem3268479 A) (@lem3268478 A)). Qed.
Lemma lem3268481 {A : Type'} : (term252 A) = (term252 A).
Proof. exact (eq_refl (term252 A)). Qed.
Lemma lem3268482 {A : Type'} : (term256 A) = (term342 A).
Proof. exact (MK_COMB (@lem3268481 A) (@lem3268480 A)). Qed.
Lemma lem3268484 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3268485 {A : Type'} (P : type686 A) (Q : type686 A) : (term193 A P Q) = (term192 A P Q).
Proof. exact (@lem3268484 (A -> Prop) P Q). Qed.
Lemma lem3268486 {A : Type'} : (term343 A) = (term344 A).
Proof. exact (@lem3268485 A (term239 A) (term340 A)). Qed.
Lemma lem3268487 {A : Type'} (s : A -> Prop) : (term241 A s) = (term228 A s).
Proof. exact (eq_refl (term241 A s)). Qed.
Lemma lem3268488 {A : Type'} : (term248 A) = (term239 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268487 A s)). Qed.
Lemma lem3268489 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268490 {A : Type'} : (term249 A) = (term250 A).
Proof. exact (MK_COMB (@lem3268489 A) (@lem3268488 A)). Qed.
Lemma lem3268491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268492 {A : Type'} : (term251 A) = (term252 A).
Proof. exact (MK_COMB (@lem3268491) (@lem3268490 A)). Qed.
Lemma lem3268493 {A : Type'} (s : A -> Prop) : (term345 A s) = (term339 A s).
Proof. exact (eq_refl (term345 A s)). Qed.
Lemma lem3268494 {A : Type'} : (term346 A) = (term340 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268493 A s)). Qed.
Lemma lem3268495 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268496 {A : Type'} : (term347 A) = (term341 A).
Proof. exact (MK_COMB (@lem3268495 A) (@lem3268494 A)). Qed.
Lemma lem3268497 {A : Type'} : (term343 A) = (term342 A).
Proof. exact (MK_COMB (@lem3268492 A) (@lem3268496 A)). Qed.
Lemma lem3268498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268499 {A : Type'} : (term348 A) = (term349 A).
Proof. exact (MK_COMB (@lem3268498) (@lem3268497 A)). Qed.
Lemma lem3268500 {A : Type'} (s : A -> Prop) : (term241 A s) = (term228 A s).
Proof. exact (eq_refl (term241 A s)). Qed.
Lemma lem3268501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268502 {A : Type'} (s : A -> Prop) : (term242 A s) = (term230 A s).
Proof. exact (MK_COMB (@lem3268501) (@lem3268500 A s)). Qed.
Lemma lem3268503 {A : Type'} (s : A -> Prop) : (term345 A s) = (term339 A s).
Proof. exact (eq_refl (term345 A s)). Qed.
Lemma lem3268504 {A : Type'} (s : A -> Prop) : (term350 A s) = (term351 A s).
Proof. exact (MK_COMB (@lem3268502 A s) (@lem3268503 A s)). Qed.
Lemma lem3268505 {A : Type'} : (term352 A) = (term353 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268504 A s)). Qed.
Lemma lem3268506 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268507 {A : Type'} : (term344 A) = (term354 A).
Proof. exact (MK_COMB (@lem3268506 A) (@lem3268505 A)). Qed.
Lemma lem3268508 {A : Type'} : ((term343 A) = (term344 A)) = ((term342 A) = (term354 A)).
Proof. exact (MK_COMB (@lem3268499 A) (@lem3268507 A)). Qed.
Lemma lem3268509 {A : Type'} : (term342 A) = (term354 A).
Proof. exact (EQ_MP (@lem3268508 A) (@lem3268486 A)). Qed.
Lemma lem3268511 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3268512 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (@lem3268511 A P Q). Qed.
Lemma lem3268513 {A : Type'} (s : A -> Prop) : (term355 A s) = (term356 A s).
Proof. exact (@lem3268512 A (term217 A s) (term338 A s)). Qed.
Lemma lem3268514 {A : Type'} (s : A -> Prop) (a : A) : (term219 A s a) = (term144 A s a).
Proof. exact (eq_refl (term219 A s a)). Qed.
Lemma lem3268515 {A : Type'} (s : A -> Prop) : (term226 A s) = (term217 A s).
Proof. exact (fun_ext (fun a : A => @lem3268514 A s a)). Qed.
Lemma lem3268516 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268517 {A : Type'} (s : A -> Prop) : (term227 A s) = (term228 A s).
Proof. exact (MK_COMB (@lem3268516 A) (@lem3268515 A s)). Qed.
Lemma lem3268518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268519 {A : Type'} (s : A -> Prop) : (term229 A s) = (term230 A s).
Proof. exact (MK_COMB (@lem3268518) (@lem3268517 A s)). Qed.
Lemma lem3268520 {A : Type'} (s : A -> Prop) (a : A) : (term357 A s a) = (term337 A s a).
Proof. exact (eq_refl (term357 A s a)). Qed.
Lemma lem3268521 {A : Type'} (s : A -> Prop) : (term358 A s) = (term338 A s).
Proof. exact (fun_ext (fun a : A => @lem3268520 A s a)). Qed.
Lemma lem3268522 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268523 {A : Type'} (s : A -> Prop) : (term359 A s) = (term339 A s).
Proof. exact (MK_COMB (@lem3268522 A) (@lem3268521 A s)). Qed.
Lemma lem3268524 {A : Type'} (s : A -> Prop) : (term355 A s) = (term351 A s).
Proof. exact (MK_COMB (@lem3268519 A s) (@lem3268523 A s)). Qed.
Lemma lem3268525 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268526 {A : Type'} (s : A -> Prop) : (term360 A s) = (term361 A s).
Proof. exact (MK_COMB (@lem3268525) (@lem3268524 A s)). Qed.
Lemma lem3268527 {A : Type'} (s : A -> Prop) (a : A) : (term219 A s a) = (term144 A s a).
Proof. exact (eq_refl (term219 A s a)). Qed.
Lemma lem3268528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268529 {A : Type'} (s : A -> Prop) (a : A) : (term220 A s a) = (term146 A s a).
Proof. exact (MK_COMB (@lem3268528) (@lem3268527 A s a)). Qed.
Lemma lem3268530 {A : Type'} (s : A -> Prop) (a : A) : (term357 A s a) = (term337 A s a).
Proof. exact (eq_refl (term357 A s a)). Qed.
Lemma lem3268531 {A : Type'} (s : A -> Prop) (a : A) : (term362 A s a) = (term363 A s a).
Proof. exact (MK_COMB (@lem3268529 A s a) (@lem3268530 A s a)). Qed.
Lemma lem3268532 {A : Type'} (s : A -> Prop) : (term364 A s) = (term365 A s).
Proof. exact (fun_ext (fun a : A => @lem3268531 A s a)). Qed.
Lemma lem3268533 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268534 {A : Type'} (s : A -> Prop) : (term356 A s) = (term366 A s).
Proof. exact (MK_COMB (@lem3268533 A) (@lem3268532 A s)). Qed.
Lemma lem3268535 {A : Type'} (s : A -> Prop) : ((term355 A s) = (term356 A s)) = ((term351 A s) = (term366 A s)).
Proof. exact (MK_COMB (@lem3268526 A s) (@lem3268534 A s)). Qed.
Lemma lem3268536 {A : Type'} (s : A -> Prop) : (term351 A s) = (term366 A s).
Proof. exact (EQ_MP (@lem3268535 A s) (@lem3268513 A s)). Qed.
Lemma lem3268538 {A : Type'} (P : Prop) (Q : A -> Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3268539 {A : Type'} (P : Prop) (Q : A -> Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (@lem3268538 A P Q). Qed.
Lemma lem3268540 {A : Type'} (s : A -> Prop) (a : A) : (term367 A s a) = (term368 A s a).
Proof. exact (@lem3268539 A (term144 A s a) (term336 A s a)). Qed.
Lemma lem3268541 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term369 A s a x) = (term334 A x s a).
Proof. exact (eq_refl (term369 A s a x)). Qed.
Lemma lem3268542 {A : Type'} (s : A -> Prop) (a : A) : (term370 A s a) = (term336 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268541 A x s a)). Qed.
Lemma lem3268543 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268544 {A : Type'} (s : A -> Prop) (a : A) : (term371 A s a) = (term337 A s a).
Proof. exact (MK_COMB (@lem3268543 A) (@lem3268542 A s a)). Qed.
Lemma lem3268545 {A : Type'} (s : A -> Prop) (a : A) : (term146 A s a) = (term146 A s a).
Proof. exact (eq_refl (term146 A s a)). Qed.
Lemma lem3268546 {A : Type'} (s : A -> Prop) (a : A) : (term367 A s a) = (term363 A s a).
Proof. exact (MK_COMB (@lem3268545 A s a) (@lem3268544 A s a)). Qed.
Lemma lem3268547 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268548 {A : Type'} (s : A -> Prop) (a : A) : (term372 A s a) = (term373 A s a).
Proof. exact (MK_COMB (@lem3268547) (@lem3268546 A s a)). Qed.
Lemma lem3268549 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term369 A s a x) = (term334 A x s a).
Proof. exact (eq_refl (term369 A s a x)). Qed.
Lemma lem3268550 {A : Type'} (s : A -> Prop) (a : A) : (term146 A s a) = (term146 A s a).
Proof. exact (eq_refl (term146 A s a)). Qed.
Lemma lem3268551 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term374 A s a x) = (term375 A x s a).
Proof. exact (MK_COMB (@lem3268550 A s a) (@lem3268549 A x s a)). Qed.
Lemma lem3268552 {A : Type'} (s : A -> Prop) (a : A) : (term376 A s a) = (term377 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268551 A x s a)). Qed.
Lemma lem3268553 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268554 {A : Type'} (s : A -> Prop) (a : A) : (term368 A s a) = (term378 A s a).
Proof. exact (MK_COMB (@lem3268553 A) (@lem3268552 A s a)). Qed.
Lemma lem3268555 {A : Type'} (s : A -> Prop) (a : A) : ((term367 A s a) = (term368 A s a)) = ((term363 A s a) = (term378 A s a)).
Proof. exact (MK_COMB (@lem3268548 A s a) (@lem3268554 A s a)). Qed.
Lemma lem3268556 {A : Type'} (s : A -> Prop) (a : A) : (term363 A s a) = (term378 A s a).
Proof. exact (EQ_MP (@lem3268555 A s a) (@lem3268540 A s a)). Qed.
Lemma lem3268557 {A : Type'} (s : A -> Prop) : (term365 A s) = (term379 A s).
Proof. exact (fun_ext (fun a : A => @lem3268556 A s a)). Qed.
Lemma lem3268558 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268559 {A : Type'} (s : A -> Prop) : (term366 A s) = (term380 A s).
Proof. exact (MK_COMB (@lem3268558 A) (@lem3268557 A s)). Qed.
Lemma lem3268560 {A : Type'} (s : A -> Prop) : (term351 A s) = (term380 A s).
Proof. exact (TRANS (@lem3268536 A s) (@lem3268559 A s)). Qed.
Lemma lem3268561 {A : Type'} : (term353 A) = (term381 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268560 A s)). Qed.
Lemma lem3268562 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268563 {A : Type'} : (term354 A) = (term382 A).
Proof. exact (MK_COMB (@lem3268562 A) (@lem3268561 A)). Qed.
Lemma lem3268564 {A : Type'} : (term342 A) = (term382 A).
Proof. exact (TRANS (@lem3268509 A) (@lem3268563 A)). Qed.
Lemma lem3268565 {A : Type'} : (term256 A) = (term382 A).
Proof. exact (TRANS (@lem3268482 A) (@lem3268564 A)). Qed.
Lemma lem3268566 {A : Type'} : (term257 A) = (term383 A).
Proof. exact (MK_COMB (@lem3268450 A) (@lem3268565 A)). Qed.
Lemma lem3268568 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3268569 {A : Type'} (P : type686 A) (Q : type686 A) : (term193 A P Q) = (term192 A P Q).
Proof. exact (@lem3268568 (A -> Prop) P Q). Qed.
Lemma lem3268570 {A : Type'} : (term384 A) = (term385 A).
Proof. exact (@lem3268569 A (term320 A) (term381 A)). Qed.
Lemma lem3268571 {A : Type'} (s : A -> Prop) : (term386 A s) = (term319 A s).
Proof. exact (eq_refl (term386 A s)). Qed.
Lemma lem3268572 {A : Type'} : (term387 A) = (term320 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268571 A s)). Qed.
Lemma lem3268573 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268574 {A : Type'} : (term388 A) = (term321 A).
Proof. exact (MK_COMB (@lem3268573 A) (@lem3268572 A)). Qed.
Lemma lem3268575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268576 {A : Type'} : (term389 A) = (term322 A).
Proof. exact (MK_COMB (@lem3268575) (@lem3268574 A)). Qed.
Lemma lem3268577 {A : Type'} (s : A -> Prop) : (term390 A s) = (term380 A s).
Proof. exact (eq_refl (term390 A s)). Qed.
Lemma lem3268578 {A : Type'} : (term391 A) = (term381 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268577 A s)). Qed.
Lemma lem3268579 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268580 {A : Type'} : (term392 A) = (term382 A).
Proof. exact (MK_COMB (@lem3268579 A) (@lem3268578 A)). Qed.
Lemma lem3268581 {A : Type'} : (term384 A) = (term383 A).
Proof. exact (MK_COMB (@lem3268576 A) (@lem3268580 A)). Qed.
Lemma lem3268582 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268583 {A : Type'} : (term393 A) = (term394 A).
Proof. exact (MK_COMB (@lem3268582) (@lem3268581 A)). Qed.
Lemma lem3268584 {A : Type'} (s : A -> Prop) : (term386 A s) = (term319 A s).
Proof. exact (eq_refl (term386 A s)). Qed.
Lemma lem3268585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268586 {A : Type'} (s : A -> Prop) : (term395 A s) = (term396 A s).
Proof. exact (MK_COMB (@lem3268585) (@lem3268584 A s)). Qed.
Lemma lem3268587 {A : Type'} (s : A -> Prop) : (term390 A s) = (term380 A s).
Proof. exact (eq_refl (term390 A s)). Qed.
Lemma lem3268588 {A : Type'} (s : A -> Prop) : (term397 A s) = (term398 A s).
Proof. exact (MK_COMB (@lem3268586 A s) (@lem3268587 A s)). Qed.
Lemma lem3268589 {A : Type'} : (term399 A) = (term400 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268588 A s)). Qed.
Lemma lem3268590 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268591 {A : Type'} : (term385 A) = (term401 A).
Proof. exact (MK_COMB (@lem3268590 A) (@lem3268589 A)). Qed.
Lemma lem3268592 {A : Type'} : ((term384 A) = (term385 A)) = ((term383 A) = (term401 A)).
Proof. exact (MK_COMB (@lem3268583 A) (@lem3268591 A)). Qed.
Lemma lem3268593 {A : Type'} : (term383 A) = (term401 A).
Proof. exact (EQ_MP (@lem3268592 A) (@lem3268570 A)). Qed.
Lemma lem3268595 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3268596 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (@lem3268595 A P Q). Qed.
Lemma lem3268597 {A : Type'} (s : A -> Prop) : (term402 A s) = (term403 A s).
Proof. exact (@lem3268596 A (term318 A s) (term379 A s)). Qed.
Lemma lem3268598 {A : Type'} (s : A -> Prop) (a : A) : (term404 A s a) = (term317 A s a).
Proof. exact (eq_refl (term404 A s a)). Qed.
Lemma lem3268599 {A : Type'} (s : A -> Prop) : (term405 A s) = (term318 A s).
Proof. exact (fun_ext (fun a : A => @lem3268598 A s a)). Qed.
Lemma lem3268600 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268601 {A : Type'} (s : A -> Prop) : (term406 A s) = (term319 A s).
Proof. exact (MK_COMB (@lem3268600 A) (@lem3268599 A s)). Qed.
Lemma lem3268602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268603 {A : Type'} (s : A -> Prop) : (term407 A s) = (term396 A s).
Proof. exact (MK_COMB (@lem3268602) (@lem3268601 A s)). Qed.
Lemma lem3268604 {A : Type'} (s : A -> Prop) (a : A) : (term408 A s a) = (term378 A s a).
Proof. exact (eq_refl (term408 A s a)). Qed.
Lemma lem3268605 {A : Type'} (s : A -> Prop) : (term409 A s) = (term379 A s).
Proof. exact (fun_ext (fun a : A => @lem3268604 A s a)). Qed.
Lemma lem3268606 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268607 {A : Type'} (s : A -> Prop) : (term410 A s) = (term380 A s).
Proof. exact (MK_COMB (@lem3268606 A) (@lem3268605 A s)). Qed.
Lemma lem3268608 {A : Type'} (s : A -> Prop) : (term402 A s) = (term398 A s).
Proof. exact (MK_COMB (@lem3268603 A s) (@lem3268607 A s)). Qed.
Lemma lem3268609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268610 {A : Type'} (s : A -> Prop) : (term411 A s) = (term412 A s).
Proof. exact (MK_COMB (@lem3268609) (@lem3268608 A s)). Qed.
Lemma lem3268611 {A : Type'} (s : A -> Prop) (a : A) : (term404 A s a) = (term317 A s a).
Proof. exact (eq_refl (term404 A s a)). Qed.
Lemma lem3268612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268613 {A : Type'} (s : A -> Prop) (a : A) : (term413 A s a) = (term414 A s a).
Proof. exact (MK_COMB (@lem3268612) (@lem3268611 A s a)). Qed.
Lemma lem3268614 {A : Type'} (s : A -> Prop) (a : A) : (term408 A s a) = (term378 A s a).
Proof. exact (eq_refl (term408 A s a)). Qed.
Lemma lem3268615 {A : Type'} (s : A -> Prop) (a : A) : (term415 A s a) = (term416 A s a).
Proof. exact (MK_COMB (@lem3268613 A s a) (@lem3268614 A s a)). Qed.
Lemma lem3268616 {A : Type'} (s : A -> Prop) : (term417 A s) = (term418 A s).
Proof. exact (fun_ext (fun a : A => @lem3268615 A s a)). Qed.
Lemma lem3268617 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268618 {A : Type'} (s : A -> Prop) : (term403 A s) = (term419 A s).
Proof. exact (MK_COMB (@lem3268617 A) (@lem3268616 A s)). Qed.
Lemma lem3268619 {A : Type'} (s : A -> Prop) : ((term402 A s) = (term403 A s)) = ((term398 A s) = (term419 A s)).
Proof. exact (MK_COMB (@lem3268610 A s) (@lem3268618 A s)). Qed.
Lemma lem3268620 {A : Type'} (s : A -> Prop) : (term398 A s) = (term419 A s).
Proof. exact (EQ_MP (@lem3268619 A s) (@lem3268597 A s)). Qed.
Lemma lem3268622 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3268623 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (@lem3268622 A P Q). Qed.
Lemma lem3268624 {A : Type'} (s : A -> Prop) (a : A) : (term420 A s a) = (term421 A s a).
Proof. exact (@lem3268623 A (term316 A s a) (term377 A s a)). Qed.
Lemma lem3268625 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term422 A s a x) = (term314 A x s a).
Proof. exact (eq_refl (term422 A s a x)). Qed.
Lemma lem3268626 {A : Type'} (s : A -> Prop) (a : A) : (term423 A s a) = (term316 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268625 A x s a)). Qed.
Lemma lem3268627 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268628 {A : Type'} (s : A -> Prop) (a : A) : (term424 A s a) = (term317 A s a).
Proof. exact (MK_COMB (@lem3268627 A) (@lem3268626 A s a)). Qed.
Lemma lem3268629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268630 {A : Type'} (s : A -> Prop) (a : A) : (term425 A s a) = (term414 A s a).
Proof. exact (MK_COMB (@lem3268629) (@lem3268628 A s a)). Qed.
Lemma lem3268631 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term426 A s a x) = (term375 A x s a).
Proof. exact (eq_refl (term426 A s a x)). Qed.
Lemma lem3268632 {A : Type'} (s : A -> Prop) (a : A) : (term427 A s a) = (term377 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268631 A x s a)). Qed.
Lemma lem3268633 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268634 {A : Type'} (s : A -> Prop) (a : A) : (term428 A s a) = (term378 A s a).
Proof. exact (MK_COMB (@lem3268633 A) (@lem3268632 A s a)). Qed.
Lemma lem3268635 {A : Type'} (s : A -> Prop) (a : A) : (term420 A s a) = (term416 A s a).
Proof. exact (MK_COMB (@lem3268630 A s a) (@lem3268634 A s a)). Qed.
Lemma lem3268636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268637 {A : Type'} (s : A -> Prop) (a : A) : (term429 A s a) = (term430 A s a).
Proof. exact (MK_COMB (@lem3268636) (@lem3268635 A s a)). Qed.
Lemma lem3268638 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term422 A s a x) = (term314 A x s a).
Proof. exact (eq_refl (term422 A s a x)). Qed.
Lemma lem3268639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268640 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term431 A s a x) = (term432 A x s a).
Proof. exact (MK_COMB (@lem3268639) (@lem3268638 A x s a)). Qed.
Lemma lem3268641 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term426 A s a x) = (term375 A x s a).
Proof. exact (eq_refl (term426 A s a x)). Qed.
Lemma lem3268642 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term433 A s a x) = (term434 A x s a).
Proof. exact (MK_COMB (@lem3268640 A x s a) (@lem3268641 A x s a)). Qed.
Lemma lem3268643 {A : Type'} (s : A -> Prop) (a : A) : (term435 A s a) = (term436 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268642 A x s a)). Qed.
Lemma lem3268644 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268645 {A : Type'} (s : A -> Prop) (a : A) : (term421 A s a) = (term437 A s a).
Proof. exact (MK_COMB (@lem3268644 A) (@lem3268643 A s a)). Qed.
Lemma lem3268646 {A : Type'} (s : A -> Prop) (a : A) : ((term420 A s a) = (term421 A s a)) = ((term416 A s a) = (term437 A s a)).
Proof. exact (MK_COMB (@lem3268637 A s a) (@lem3268645 A s a)). Qed.
Lemma lem3268647 {A : Type'} (s : A -> Prop) (a : A) : (term416 A s a) = (term437 A s a).
Proof. exact (EQ_MP (@lem3268646 A s a) (@lem3268624 A s a)). Qed.
Lemma lem3268648 {A : Type'} (s : A -> Prop) : (term418 A s) = (term438 A s).
Proof. exact (fun_ext (fun a : A => @lem3268647 A s a)). Qed.
Lemma lem3268649 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3268650 {A : Type'} (s : A -> Prop) : (term419 A s) = (term439 A s).
Proof. exact (MK_COMB (@lem3268649 A) (@lem3268648 A s)). Qed.
Lemma lem3268651 {A : Type'} (s : A -> Prop) : (term398 A s) = (term439 A s).
Proof. exact (TRANS (@lem3268620 A s) (@lem3268650 A s)). Qed.
Lemma lem3268652 {A : Type'} : (term400 A) = (term440 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3268651 A s)). Qed.
Lemma lem3268653 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3268654 {A : Type'} : (term401 A) = (term441 A).
Proof. exact (MK_COMB (@lem3268653 A) (@lem3268652 A)). Qed.
Lemma lem3268655 {A : Type'} : (term383 A) = (term441 A).
Proof. exact (TRANS (@lem3268593 A) (@lem3268654 A)). Qed.
Lemma lem3268656 {A : Type'} : (term257 A) = (term441 A).
Proof. exact (TRANS (@lem3268566 A) (@lem3268655 A)). Qed.
Lemma lem3268657 {A : Type'} : (term167 A) = (term441 A).
Proof. exact (TRANS (@lem3268333 A) (@lem3268656 A)). Qed.
Lemma lem3268658 {A : Type'} : (term77 A) = (term441 A).
Proof. exact (TRANS (@lem3267558 A) (@lem3268657 A)). Qed.
Lemma lem3268659 {A : Type'} (h1 : term77 A) : term441 A.
Proof. exact (EQ_MP (@lem3268658 A) (@lem3267429 A h1)). Qed.
Lemma lem3268660 {A : Type'} (s : A -> Prop) (h1 : term439 A s) : term439 A s.
Proof. exact (h1). Qed.
Lemma lem3268661 {A : Type'} (s : A -> Prop) (a : A) (h1 : term437 A s a) : term437 A s a.
Proof. exact (h1). Qed.
Lemma lem3268662 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term434 A x s a) : term434 A x s a.
Proof. exact (h1). Qed.
Lemma lem3268681 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term334 A x s a) = (term334 A x s a).
Proof. exact (eq_refl (term334 A x s a)). Qed.
Lemma lem3268684 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem3268699 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term126 A a s x) = (term126 A a s x).
Proof. exact (eq_refl (term126 A a s x)). Qed.
Lemma lem3268700 {A : Type'} (a : A) (s : A -> Prop) : (term135 A a s) = (term135 A a s).
Proof. exact (fun_ext (fun x : A => @lem3268699 A a s x)). Qed.
Lemma lem3268701 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3268702 {A : Type'} (a : A) (s : A -> Prop) : (term136 A a s) = (term136 A a s).
Proof. exact (MK_COMB (@lem3268701 A) (@lem3268700 A a s)). Qed.
Lemma lem3268703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3268704 {A : Type'} (a : A) (s : A -> Prop) : (term142 A a s) = (term142 A a s).
Proof. exact (MK_COMB (@lem3268703) (@lem3268702 A a s)). Qed.
Lemma lem3268705 {A : Type'} (s : A -> Prop) (a : A) : (term144 A s a) = (term144 A s a).
Proof. exact (MK_COMB (@lem3268704 A a s) (@lem3268684 A s a)). Qed.
Lemma lem3268706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268707 {A : Type'} (s : A -> Prop) (a : A) : (term146 A s a) = (term146 A s a).
Proof. exact (MK_COMB (@lem3268706) (@lem3268705 A s a)). Qed.
Lemma lem3268708 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term375 A x s a) = (term375 A x s a).
Proof. exact (MK_COMB (@lem3268707 A s a) (@lem3268681 A x s a)). Qed.
Lemma lem3268727 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term271 A x s a) = (term271 A x s a).
Proof. exact (eq_refl (term271 A x s a)). Qed.
Lemma lem3268730 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem3268745 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term83 A s x a) = (term83 A s x a).
Proof. exact (eq_refl (term83 A s x a)). Qed.
Lemma lem3268746 {A : Type'} (s : A -> Prop) (a : A) : (term94 A s a) = (term94 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268745 A s x a)). Qed.
Lemma lem3268747 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3268748 {A : Type'} (s : A -> Prop) (a : A) : (term95 A s a) = (term95 A s a).
Proof. exact (MK_COMB (@lem3268747 A) (@lem3268746 A s a)). Qed.
Lemma lem3268749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3268750 {A : Type'} (s : A -> Prop) (a : A) : (term102 A s a) = (term102 A s a).
Proof. exact (MK_COMB (@lem3268749) (@lem3268748 A s a)). Qed.
Lemma lem3268751 {A : Type'} (s : A -> Prop) (a : A) : (term104 A s a) = (term104 A s a).
Proof. exact (MK_COMB (@lem3268750 A s a) (@lem3268730 A s a)). Qed.
Lemma lem3268752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268753 {A : Type'} (s : A -> Prop) (a : A) : (term106 A s a) = (term106 A s a).
Proof. exact (MK_COMB (@lem3268752) (@lem3268751 A s a)). Qed.
Lemma lem3268754 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term314 A x s a) = (term314 A x s a).
Proof. exact (MK_COMB (@lem3268753 A s a) (@lem3268727 A x s a)). Qed.
Lemma lem3268755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3268756 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term432 A x s a) = (term432 A x s a).
Proof. exact (MK_COMB (@lem3268755) (@lem3268754 A x s a)). Qed.
Lemma lem3268757 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term434 A x s a) = (term434 A x s a).
Proof. exact (MK_COMB (@lem3268756 A x s a) (@lem3268708 A x s a)). Qed.
Lemma lem3268758 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term434 A x s a) : term434 A x s a.
Proof. exact (EQ_MP (@lem3268757 A x s a) (@lem3268662 A x s a h1)). Qed.
Lemma lem3268759 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term314 A x s a) : term314 A x s a.
Proof. exact (h1). Qed.
Lemma lem3268760 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term375 A x s a) : term375 A x s a.
Proof. exact (h1). Qed.
Lemma lem3268761 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : term104 A s a.
Proof. exact (h1). Qed.
Lemma lem3268762 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : term271 A x s a.
Proof. exact (h1). Qed.
Lemma lem3268764 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : term95 A s a.
Proof. exact (proj1 (@lem3268761 A s a h1)). Qed.
Lemma lem3268766 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : term44 A s x a.
Proof. exact (proj1 (@lem3268762 A x s a h1)). Qed.
Lemma lem3268769 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : term144 A s a.
Proof. exact (h1). Qed.
Lemma lem3268770 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : term334 A x s a.
Proof. exact (h1). Qed.
Lemma lem3268772 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : term136 A a s.
Proof. exact (proj1 (@lem3268769 A s a h1)). Qed.
Lemma lem3268774 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : term62 A a s x.
Proof. exact (proj1 (@lem3268770 A x s a h1)). Qed.
Lemma lem3268784 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term83 A s x a) = (term83 A s x a).
Proof. exact (eq_refl (term83 A s x a)). Qed.
Lemma lem3268785 {A : Type'} (s : A -> Prop) (a : A) : (term94 A s a) = (term94 A s a).
Proof. exact (fun_ext (fun x : A => @lem3268784 A s x a)). Qed.
Lemma lem3268786 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3268788 {A : Type'} (s : A -> Prop) (a : A) : (term95 A s a) = (term95 A s a).
Proof. exact (MK_COMB (@lem3268786 A) (@lem3268785 A s a)). Qed.
Lemma lem3268789 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : term95 A s a.
Proof. exact (EQ_MP (@lem3268788 A s a) (@lem3268764 A s a h1)). Qed.
Lemma lem3268813 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term126 A a s x) = (term126 A a s x).
Proof. exact (eq_refl (term126 A a s x)). Qed.
Lemma lem3268814 {A : Type'} (a : A) (s : A -> Prop) : (term135 A a s) = (term135 A a s).
Proof. exact (fun_ext (fun x : A => @lem3268813 A a s x)). Qed.
Lemma lem3268815 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3268817 {A : Type'} (a : A) (s : A -> Prop) : (term136 A a s) = (term136 A a s).
Proof. exact (MK_COMB (@lem3268815 A) (@lem3268814 A a s)). Qed.
Lemma lem3268818 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : term136 A a s.
Proof. exact (EQ_MP (@lem3268817 A a s) (@lem3268772 A s a h1)). Qed.
Lemma lem3268835 {A : Type'} (_33418 : A) (s : A -> Prop) (a : A) (h1 : term104 A s a) : term442 A s a _33418.
Proof. exact (@lem3268789 A s a h1 _33418). Qed.
Lemma lem3268836 {A : Type'} (s : A -> Prop) (_33418 : A) (a : A) : (term442 A s a _33418) = (term83 A s _33418 a).
Proof. exact (eq_refl (term442 A s a _33418)). Qed.
Lemma lem3268838 {A : Type'} (_33419 : A) (s : A -> Prop) (a : A) (h1 : term144 A s a) : term443 A a s _33419.
Proof. exact (@lem3268818 A s a h1 _33419). Qed.
Lemma lem3268839 {A : Type'} (a : A) (s : A -> Prop) (_33419 : A) : (term443 A a s _33419) = (term126 A a s _33419).
Proof. exact (eq_refl (term443 A a s _33419)). Qed.
Lemma lem3268846 {A : Type'} (_33418 : A) (s : A -> Prop) (a : A) (h1 : term104 A s a) : term83 A s _33418 a.
Proof. exact (EQ_MP (@lem3268836 A s _33418 a) (@lem3268835 A _33418 s a h1)). Qed.
Lemma lem3268852 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : s x.
Proof. exact (proj1 (@lem3268766 A x s a h1)). Qed.
Lemma lem3268854 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : x = a.
Proof. exact (proj2 (@lem3268766 A x s a h1)). Qed.
Lemma lem3268860 {A : Type'} (_33419 : A) (s : A -> Prop) (a : A) (h1 : term144 A s a) : term126 A a s _33419.
Proof. exact (EQ_MP (@lem3268839 A a s _33419) (@lem3268838 A _33419 s a h1)). Qed.
Lemma lem3268866 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : x = a.
Proof. exact (proj1 (@lem3268774 A x s a h1)). Qed.
Lemma lem3268868 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : s x.
Proof. exact (proj2 (@lem3268774 A x s a h1)). Qed.
Lemma lem3268896 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : term52 A s a.
Proof. exact (proj2 (@lem3268762 A x s a h1)). Qed.
Lemma lem3268897 {A : Type'} (s : A -> Prop) : (term444 A s) = (term444 A s).
Proof. exact (eq_refl (term444 A s)). Qed.
Lemma lem3268898 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : (term445 A s x) = (term445 A s a).
Proof. exact (MK_COMB (@lem3268897 A s) (@lem3268854 A x s a h1)). Qed.
Lemma lem3268899 {A : Type'} (s : A -> Prop) (a : A) : (term445 A s a) = (s a).
Proof. exact (eq_refl (term445 A s a)). Qed.
Lemma lem3268900 {A : Type'} (s : A -> Prop) (x : A) : (term446 A s x) = (term446 A s x).
Proof. exact (eq_refl (term446 A s x)). Qed.
Lemma lem3268901 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term445 A s x) = (term445 A s a)) = ((term445 A s x) = (s a)).
Proof. exact (MK_COMB (@lem3268900 A s x) (@lem3268899 A s a)). Qed.
Lemma lem3268902 {A : Type'} (s : A -> Prop) (x : A) : (term445 A s x) = (s x).
Proof. exact (eq_refl (term445 A s x)). Qed.
Lemma lem3268903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268904 {A : Type'} (s : A -> Prop) (x : A) : (term446 A s x) = (term447 A s x).
Proof. exact (MK_COMB (@lem3268903) (@lem3268902 A s x)). Qed.
Lemma lem3268905 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem3268906 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term445 A s x) = (s a)) = ((s x) = (s a)).
Proof. exact (MK_COMB (@lem3268904 A s x) (@lem3268905 A s a)). Qed.
Lemma lem3268907 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term445 A s x) = (term445 A s a)) = ((s x) = (s a)).
Proof. exact (TRANS (@lem3268901 A x s a) (@lem3268906 A x s a)). Qed.
Lemma lem3268908 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : (s x) = (s a).
Proof. exact (EQ_MP (@lem3268907 A x s a) (@lem3268898 A x s a h1)). Qed.
Lemma lem3268937 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : term52 A s a.
Proof. exact (proj2 (@lem3268770 A x s a h1)). Qed.
Lemma lem3268938 {A : Type'} (s : A -> Prop) : (term444 A s) = (term444 A s).
Proof. exact (eq_refl (term444 A s)). Qed.
Lemma lem3268939 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : (term445 A s x) = (term445 A s a).
Proof. exact (MK_COMB (@lem3268938 A s) (@lem3268866 A x s a h1)). Qed.
Lemma lem3268940 {A : Type'} (s : A -> Prop) (a : A) : (term445 A s a) = (s a).
Proof. exact (eq_refl (term445 A s a)). Qed.
Lemma lem3268941 {A : Type'} (s : A -> Prop) (x : A) : (term446 A s x) = (term446 A s x).
Proof. exact (eq_refl (term446 A s x)). Qed.
Lemma lem3268942 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term445 A s x) = (term445 A s a)) = ((term445 A s x) = (s a)).
Proof. exact (MK_COMB (@lem3268941 A s x) (@lem3268940 A s a)). Qed.
Lemma lem3268943 {A : Type'} (s : A -> Prop) (x : A) : (term445 A s x) = (s x).
Proof. exact (eq_refl (term445 A s x)). Qed.
Lemma lem3268944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3268945 {A : Type'} (s : A -> Prop) (x : A) : (term446 A s x) = (term447 A s x).
Proof. exact (MK_COMB (@lem3268944) (@lem3268943 A s x)). Qed.
Lemma lem3268946 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem3268947 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term445 A s x) = (s a)) = ((s x) = (s a)).
Proof. exact (MK_COMB (@lem3268945 A s x) (@lem3268946 A s a)). Qed.
Lemma lem3268948 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term445 A s x) = (term445 A s a)) = ((s x) = (s a)).
Proof. exact (TRANS (@lem3268942 A x s a) (@lem3268947 A x s a)). Qed.
Lemma lem3268949 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : (s x) = (s a).
Proof. exact (EQ_MP (@lem3268948 A x s a) (@lem3268939 A x s a h1)). Qed.
Lemma lem3268966 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : s a.
Proof. exact (proj2 (@lem3268761 A s a h1)). Qed.
Lemma lem3268967 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : term448 A s a.
Proof. exact (fun h0 : term52 A s a => @lem3268966 A s a h1). Qed.
Lemma lem3268969 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3268970 {A : Type'} (s : A -> Prop) (a : A) : (term448 A s a) = (s a).
Proof. exact (@lem3268969 (s a)). Qed.
Lemma lem3268971 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : s a.
Proof. exact (EQ_MP (@lem3268970 A s a) (@lem3268967 A s a h1)). Qed.
Lemma lem3268973 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3268974 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3268973 A x). Qed.
Lemma lem3268975 {A : Type'} (a : A) : a = a.
Proof. exact (@lem3268974 A a). Qed.
Lemma lem3268976 {A : Type'} (a : A) : term450 A a.
Proof. exact (fun h0 : term451 A a => @lem3268975 A a). Qed.
Lemma lem3268978 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3268979 {A : Type'} (a : A) : (term450 A a) = (a = a).
Proof. exact (@lem3268978 (a = a)). Qed.
Lemma lem3268980 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem3268979 A a) (@lem3268976 A a)). Qed.
Lemma lem3268982 (a : Prop) (b : Prop) : (term452 a b) = (term453 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3268983 {A : Type'} (s : A -> Prop) (_33418 : A) (a : A) : (term83 A s _33418 a) = (term47 A s _33418 a).
Proof. exact (@lem3268982 (s _33418) (_33418 = a)). Qed.
Lemma lem3268985 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3268986 {A : Type'} (s : A -> Prop) (_33418 : A) (a : A) : (term47 A s _33418 a) = (term454 A s _33418 a).
Proof. exact (@lem3268985 (term44 A s _33418 a)). Qed.
Lemma lem3268987 {A : Type'} (s : A -> Prop) (_33418 : A) (a : A) : (term83 A s _33418 a) = (term454 A s _33418 a).
Proof. exact (TRANS (@lem3268983 A s _33418 a) (@lem3268986 A s _33418 a)). Qed.
Lemma lem3268989 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : term455 A s a.
Proof. exact (conj (@lem3268971 A s a h1) (@lem3268980 A a)). Qed.
Lemma lem3268991 {A : Type'} (_33418 : A) (s : A -> Prop) (a : A) (h1 : term104 A s a) : term454 A s _33418 a.
Proof. exact (EQ_MP (@lem3268987 A s _33418 a) (@lem3268846 A _33418 s a h1)). Qed.
Lemma lem3268992 {A : Type'} (_33418 : A) (s : A -> Prop) (a : A) (h1 : term104 A s a) : term454 A s _33418 a.
Proof. exact (@lem3268991 A _33418 s a h1). Qed.
Lemma lem3268993 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : term456 A s a.
Proof. exact (@lem3268992 A a s a h1). Qed.
Lemma lem3268996 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : False.
Proof. exact (@lem3268993 A s a h1 (@lem3268989 A s a h1)). Qed.
Lemma lem3268997 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : term457.
Proof. exact (fun h0 : ~ False => @lem3268996 A s a h1). Qed.
Lemma lem3268999 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269000 : term457 = False.
Proof. exact (@lem3268999 False). Qed.
Lemma lem3269001 {A : Type'} (s : A -> Prop) (a : A) (h1 : term104 A s a) : False.
Proof. exact (EQ_MP (@lem3269000) (@lem3268997 A s a h1)). Qed.
Lemma lem3269003 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : s a.
Proof. exact (EQ_MP (@lem3268908 A x s a h1) (@lem3268852 A x s a h1)). Qed.
Lemma lem3269004 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : term448 A s a.
Proof. exact (fun h0 : term52 A s a => @lem3269003 A x s a h1). Qed.
Lemma lem3269006 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269007 {A : Type'} (s : A -> Prop) (a : A) : (term448 A s a) = (s a).
Proof. exact (@lem3269006 (s a)). Qed.
Lemma lem3269008 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : s a.
Proof. exact (EQ_MP (@lem3269007 A s a) (@lem3269004 A x s a h1)). Qed.
Lemma lem3269011 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3269013 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term458 A s a).
Proof. exact (@lem3269011 (s a)). Qed.
Lemma lem3269016 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : term458 A s a.
Proof. exact (EQ_MP (@lem3269013 A s a) (@lem3268896 A x s a h1)). Qed.
Lemma lem3269019 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : False.
Proof. exact (@lem3269016 A x s a h1 (@lem3269008 A x s a h1)). Qed.
Lemma lem3269020 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : term457.
Proof. exact (fun h0 : ~ False => @lem3269019 A x s a h1). Qed.
Lemma lem3269022 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269023 : term457 = False.
Proof. exact (@lem3269022 False). Qed.
Lemma lem3269040 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3269041 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3269040 A x). Qed.
Lemma lem3269042 {A : Type'} (a : A) : a = a.
Proof. exact (@lem3269041 A a). Qed.
Lemma lem3269043 {A : Type'} (a : A) : term450 A a.
Proof. exact (fun h0 : term451 A a => @lem3269042 A a). Qed.
Lemma lem3269045 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269046 {A : Type'} (a : A) : (term450 A a) = (a = a).
Proof. exact (@lem3269045 (a = a)). Qed.
Lemma lem3269047 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem3269046 A a) (@lem3269043 A a)). Qed.
Lemma lem3269049 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : s a.
Proof. exact (proj2 (@lem3268769 A s a h1)). Qed.
Lemma lem3269050 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : term448 A s a.
Proof. exact (fun h0 : term52 A s a => @lem3269049 A s a h1). Qed.
Lemma lem3269052 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269053 {A : Type'} (s : A -> Prop) (a : A) : (term448 A s a) = (s a).
Proof. exact (@lem3269052 (s a)). Qed.
Lemma lem3269054 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : s a.
Proof. exact (EQ_MP (@lem3269053 A s a) (@lem3269050 A s a h1)). Qed.
Lemma lem3269056 (a : Prop) (b : Prop) : (term452 a b) = (term453 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3269057 {A : Type'} (a : A) (s : A -> Prop) (_33419 : A) : (term126 A a s _33419) = (term65 A a s _33419).
Proof. exact (@lem3269056 (_33419 = a) (s _33419)). Qed.
Lemma lem3269059 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3269060 {A : Type'} (a : A) (s : A -> Prop) (_33419 : A) : (term65 A a s _33419) = (term459 A a s _33419).
Proof. exact (@lem3269059 (term62 A a s _33419)). Qed.
Lemma lem3269061 {A : Type'} (a : A) (s : A -> Prop) (_33419 : A) : (term126 A a s _33419) = (term459 A a s _33419).
Proof. exact (TRANS (@lem3269057 A a s _33419) (@lem3269060 A a s _33419)). Qed.
Lemma lem3269063 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : term460 A s a.
Proof. exact (conj (@lem3269047 A a) (@lem3269054 A s a h1)). Qed.
Lemma lem3269065 {A : Type'} (_33419 : A) (s : A -> Prop) (a : A) (h1 : term144 A s a) : term459 A a s _33419.
Proof. exact (EQ_MP (@lem3269061 A a s _33419) (@lem3268860 A _33419 s a h1)). Qed.
Lemma lem3269066 {A : Type'} (_33419 : A) (s : A -> Prop) (a : A) (h1 : term144 A s a) : term459 A a s _33419.
Proof. exact (@lem3269065 A _33419 s a h1). Qed.
Lemma lem3269067 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : term461 A s a.
Proof. exact (@lem3269066 A a s a h1). Qed.
Lemma lem3269070 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : False.
Proof. exact (@lem3269067 A s a h1 (@lem3269063 A s a h1)). Qed.
Lemma lem3269071 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : term457.
Proof. exact (fun h0 : ~ False => @lem3269070 A s a h1). Qed.
Lemma lem3269073 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269074 : term457 = False.
Proof. exact (@lem3269073 False). Qed.
Lemma lem3269075 {A : Type'} (s : A -> Prop) (a : A) (h1 : term144 A s a) : False.
Proof. exact (EQ_MP (@lem3269074) (@lem3269071 A s a h1)). Qed.
Lemma lem3269077 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : s a.
Proof. exact (EQ_MP (@lem3268949 A x s a h1) (@lem3268868 A x s a h1)). Qed.
Lemma lem3269078 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : term448 A s a.
Proof. exact (fun h0 : term52 A s a => @lem3269077 A x s a h1). Qed.
Lemma lem3269080 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269081 {A : Type'} (s : A -> Prop) (a : A) : (term448 A s a) = (s a).
Proof. exact (@lem3269080 (s a)). Qed.
Lemma lem3269082 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : s a.
Proof. exact (EQ_MP (@lem3269081 A s a) (@lem3269078 A x s a h1)). Qed.
Lemma lem3269085 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3269087 {A : Type'} (s : A -> Prop) (a : A) : (term52 A s a) = (term458 A s a).
Proof. exact (@lem3269085 (s a)). Qed.
Lemma lem3269090 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : term458 A s a.
Proof. exact (EQ_MP (@lem3269087 A s a) (@lem3268937 A x s a h1)). Qed.
Lemma lem3269093 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : False.
Proof. exact (@lem3269090 A x s a h1 (@lem3269082 A x s a h1)). Qed.
Lemma lem3269094 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : term457.
Proof. exact (fun h0 : ~ False => @lem3269093 A x s a h1). Qed.
Lemma lem3269096 (p : Prop) : (term449 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269097 : term457 = False.
Proof. exact (@lem3269096 False). Qed.
Lemma lem3269099 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term334 A x s a) : False.
Proof. exact (EQ_MP (@lem3269097) (@lem3269094 A x s a h1)). Qed.
Lemma lem3269100 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term271 A x s a) : False.
Proof. exact (EQ_MP (@lem3269023) (@lem3269020 A x s a h1)). Qed.
Lemma lem3269101 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term375 A x s a) : False.
Proof. exact (or_elim (@lem3268760 A x s a h1) (fun h0 : term144 A s a => @lem3269075 A s a h0) (fun h0 : term334 A x s a => @lem3269099 A x s a h0)). Qed.
Lemma lem3269102 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term314 A x s a) : False.
Proof. exact (or_elim (@lem3268759 A x s a h1) (fun h0 : term104 A s a => @lem3269001 A s a h0) (fun h0 : term271 A x s a => @lem3269100 A x s a h0)). Qed.
Lemma lem3269103 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term434 A x s a) : False.
Proof. exact (or_elim (@lem3268758 A x s a h1) (fun h0 : term314 A x s a => @lem3269102 A x s a h0) (fun h0 : term375 A x s a => @lem3269101 A x s a h0)). Qed.
Lemma lem3269104 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term434 A x s a) : (term434 A x s a) = False.
Proof. exact (prop_ext (fun h2 : term434 A x s a => @lem3269103 A x s a h1) (fun h2 : False => @lem3268758 A x s a h1)). Qed.
Lemma lem3269105 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term434 A x s a) : False.
Proof. exact (EQ_MP (@lem3269104 A x s a h1) (@lem3268758 A x s a h1)). Qed.
Lemma lem3269106 {A : Type'} (s : A -> Prop) (a : A) (h1 : term437 A s a) : False.
Proof. exact (ex_elim (@lem3268661 A s a h1) (fun x : A => fun h0 : term436 A s a x => @lem3269105 A x s a h0)). Qed.
Lemma lem3269107 {A : Type'} (s : A -> Prop) (h1 : term439 A s) : False.
Proof. exact (ex_elim (@lem3268660 A s h1) (fun a : A => fun h0 : term438 A s a => @lem3269106 A s a h0)). Qed.
Lemma lem3269108 {A : Type'} (h1 : term77 A) : False.
Proof. exact (ex_elim (@lem3268659 A h1) (fun s : A -> Prop => fun h0 : term440 A s => @lem3269107 A s h0)). Qed.
Lemma lem3269109 {A : Type'} (h1 : term77 A) : (term77 A) = False.
Proof. exact (prop_ext (fun h2 : term77 A => @lem3269108 A h1) (fun h2 : False => @lem3267429 A h1)). Qed.
Lemma lem3269110 {A : Type'} (h1 : term77 A) : False.
Proof. exact (EQ_MP (@lem3269109 A h1) (@lem3267429 A h1)). Qed.
Lemma lem3269111 {A : Type'} : term76 A.
Proof. exact (fun h0 : term77 A => @lem3269110 A h0). Qed.
Lemma lem3269112 {A : Type'} : term74 A.
Proof. exact (EQ_MP (@lem3267428 A) (@lem3269111 A)). Qed.
Lemma lem3269113 {A : Type'} : term76 A.
Proof. exact (EQ_MP (@lem3267424 A) (@lem3269112 A)). Qed.
Lemma lem3269115 {A : Type'} : term76 A.
Proof. exact (@lem3267290 A (@lem3269113 A)). Qed.
Lemma lem3269116 {A : Type'} (h1 : term77 A) : False.
Proof. exact (@lem3269115 A (@lem3267274 A h1)). Qed.
Lemma lem3269117 {A : Type'} (h1 : term77 A) : (term77 A) = False.
Proof. exact (prop_ext (fun h2 : term77 A => @lem3269116 A h1) (fun h2 : False => @lem3267274 A h1)). Qed.
Lemma lem3269118 {A : Type'} (h1 : term77 A) : False.
Proof. exact (EQ_MP (@lem3269117 A h1) (@lem3267274 A h1)). Qed.
Lemma lem3269119 {A : Type'} : term76 A.
Proof. exact (fun h0 : term77 A => @lem3269118 A h0). Qed.
Lemma lem3269120 {A : Type'} : term74 A.
Proof. exact (EQ_MP (@lem3267273 A) (@lem3269119 A)). Qed.
Lemma lem3269121 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem3267269 A) (@lem3269120 A)). Qed.
Lemma lem3269122 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem3267065 A) (@lem3269121 A)). Qed.
