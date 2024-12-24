Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CLAUSES_NUMSEG_term_abbrevs.
Require Import ITERATE_CLAUSES_NUMSEG_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Lemma lem7047121 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : term0 _123419 f op.
Proof. exact (@lem6192133 _123419 f op). Qed.
Lemma lem7047122 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term0 _123419 f op) = (term1 _123419 op f).
Proof. exact (eq_refl (term0 _123419 f op)). Qed.
Lemma lem7047125 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : term1 _123419 op f.
Proof. exact (EQ_MP (@lem7047122 _123419 op f) (@lem7047121 _123419 f op)). Qed.
Lemma lem7047126 (op : type1606) (f : nat -> nat) : term2 op f.
Proof. exact (@lem7047125 nat op f). Qed.
Lemma lem7047127 (f : nat -> nat) : term3 f.
Proof. exact (@lem7047126 Nat.add f). Qed.
Lemma lem7047128 (f : nat -> nat) : term4 f.
Proof. exact (@lem7047127 f (@lem6924403)). Qed.
Lemma lem7047144 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7047145 (m : nat) (f : nat -> nat) : (term5 m f) = (term5 m f).
Proof. exact (eq_refl (term5 m f)). Qed.
Lemma lem7047146 (m : nat) (f : nat -> nat) : (term6 m f) = (term7 m f).
Proof. exact (MK_COMB (@lem7047145 m f) (@lem7047144)). Qed.
Lemma lem7047149 (m : nat) (f : nat -> nat) : (term8 m f) = (term8 m f).
Proof. exact (eq_refl (term8 m f)). Qed.
Lemma lem7047150 (m : nat) (f : nat -> nat) : ((term9 m f) = (term6 m f)) = ((term9 m f) = (term7 m f)).
Proof. exact (MK_COMB (@lem7047149 m f) (@lem7047146 m f)). Qed.
Lemma lem7047153 (f : nat -> nat) : (term10 f) = (term11 f).
Proof. exact (fun_ext (fun m : nat => @lem7047150 m f)). Qed.
Lemma lem7047154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7047155 (f : nat -> nat) : (term12 f) = (term13 f).
Proof. exact (MK_COMB (@lem7047154) (@lem7047153 f)). Qed.
Lemma lem7047160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7047161 (f : nat -> nat) : (term14 f) = (term15 f).
Proof. exact (MK_COMB (@lem7047160) (@lem7047155 f)). Qed.
Lemma lem7047172 (f : nat -> nat) : (term16 f) = (term16 f).
Proof. exact (eq_refl (term16 f)). Qed.
Lemma lem7047173 (f : nat -> nat) : (term4 f) = (term17 f).
Proof. exact (MK_COMB (@lem7047161 f) (@lem7047172 f)). Qed.
Lemma lem7047176 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7047177 (f : nat -> nat) : (term18 f) = (term19 f).
Proof. exact (MK_COMB (@lem7047176) (@lem7047173 f)). Qed.
Lemma lem7047187 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047188 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047187 nat). Qed.
Lemma lem7047189 (m : nat) : (term20 m) = (term20 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem7047190 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem7047188) (@lem7047189 m)). Qed.
Lemma lem7047191 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047192 (m : nat) (f : nat -> nat) : (term23 m f) = (term9 m f).
Proof. exact (MK_COMB (@lem7047190 m) (@lem7047191 f)). Qed.
Lemma lem7047193 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7047194 (m : nat) (f : nat -> nat) : (term24 m f) = (term8 m f).
Proof. exact (MK_COMB (@lem7047193) (@lem7047192 m f)). Qed.
Lemma lem7047199 (m : nat) (f : nat -> nat) : (term7 m f) = (term7 m f).
Proof. exact (eq_refl (term7 m f)). Qed.
Lemma lem7047200 (m : nat) (f : nat -> nat) : ((term23 m f) = (term7 m f)) = ((term9 m f) = (term7 m f)).
Proof. exact (MK_COMB (@lem7047194 m f) (@lem7047199 m f)). Qed.
Lemma lem7047203 (f : nat -> nat) : (term25 f) = (term11 f).
Proof. exact (fun_ext (fun m : nat => @lem7047200 m f)). Qed.
Lemma lem7047204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7047205 (f : nat -> nat) : (term26 f) = (term13 f).
Proof. exact (MK_COMB (@lem7047204) (@lem7047203 f)). Qed.
Lemma lem7047210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7047211 (f : nat -> nat) : (term27 f) = (term15 f).
Proof. exact (MK_COMB (@lem7047210) (@lem7047205 f)). Qed.
Lemma lem7047223 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047224 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047223 nat). Qed.
Lemma lem7047225 (m : nat) (n : nat) : (term28 m n) = (term28 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem7047226 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem7047224) (@lem7047225 m n)). Qed.
Lemma lem7047227 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047228 (m : nat) (n : nat) (f : nat -> nat) : (term31 m n f) = (term32 m n f).
Proof. exact (MK_COMB (@lem7047226 m n) (@lem7047227 f)). Qed.
Lemma lem7047229 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7047230 (m : nat) (n : nat) (f : nat -> nat) : (term33 m n f) = (term34 m n f).
Proof. exact (MK_COMB (@lem7047229) (@lem7047228 m n f)). Qed.
Lemma lem7047232 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047233 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047232 nat). Qed.
Lemma lem7047234 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (eq_refl (dotdot m n)). Qed.
Lemma lem7047235 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem7047233) (@lem7047234 m n)). Qed.
Lemma lem7047236 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047237 (m : nat) (n : nat) (f : nat -> nat) : (term37 m n f) = (term38 m n f).
Proof. exact (MK_COMB (@lem7047235 m n) (@lem7047236 f)). Qed.
Lemma lem7047238 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7047239 (m : nat) (n : nat) (f : nat -> nat) : (term39 m n f) = (term40 m n f).
Proof. exact (MK_COMB (@lem7047238) (@lem7047237 m n f)). Qed.
Lemma lem7047240 (f : nat -> nat) (n : nat) : (term41 f n) = (term41 f n).
Proof. exact (eq_refl (term41 f n)). Qed.
Lemma lem7047241 (m : nat) (f : nat -> nat) (n : nat) : (term42 m f n) = (term43 m f n).
Proof. exact (MK_COMB (@lem7047239 m n f) (@lem7047240 f n)). Qed.
Lemma lem7047242 (m : nat) (n : nat) : (term44 m n) = (term44 m n).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem7047243 (m : nat) (f : nat -> nat) (n : nat) : (term45 m f n) = (term46 m f n).
Proof. exact (MK_COMB (@lem7047242 m n) (@lem7047241 m f n)). Qed.
Lemma lem7047245 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047246 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047245 nat). Qed.
Lemma lem7047247 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (eq_refl (dotdot m n)). Qed.
Lemma lem7047248 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem7047246) (@lem7047247 m n)). Qed.
Lemma lem7047249 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047250 (m : nat) (n : nat) (f : nat -> nat) : (term37 m n f) = (term38 m n f).
Proof. exact (MK_COMB (@lem7047248 m n) (@lem7047249 f)). Qed.
Lemma lem7047251 (m : nat) (n : nat) (f : nat -> nat) : (term47 m n f) = (term48 m n f).
Proof. exact (MK_COMB (@lem7047243 m f n) (@lem7047250 m n f)). Qed.
Lemma lem7047252 (m : nat) (n : nat) (f : nat -> nat) : ((term31 m n f) = (term47 m n f)) = ((term32 m n f) = (term48 m n f)).
Proof. exact (MK_COMB (@lem7047230 m n f) (@lem7047251 m n f)). Qed.
Lemma lem7047255 (m : nat) (f : nat -> nat) : (term49 m f) = (term50 m f).
Proof. exact (fun_ext (fun n : nat => @lem7047252 m n f)). Qed.
Lemma lem7047256 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7047257 (m : nat) (f : nat -> nat) : (term51 m f) = (term52 m f).
Proof. exact (MK_COMB (@lem7047256) (@lem7047255 m f)). Qed.
Lemma lem7047262 (f : nat -> nat) : (term53 f) = (term54 f).
Proof. exact (fun_ext (fun m : nat => @lem7047257 m f)). Qed.
Lemma lem7047263 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7047264 (f : nat -> nat) : (term55 f) = (term16 f).
Proof. exact (MK_COMB (@lem7047263) (@lem7047262 f)). Qed.
Lemma lem7047269 (f : nat -> nat) : (term56 f) = (term17 f).
Proof. exact (MK_COMB (@lem7047211 f) (@lem7047264 f)). Qed.
Lemma lem7047272 (f : nat -> nat) : (term57 f) = (term58 f).
Proof. exact (MK_COMB (@lem7047177 f) (@lem7047269 f)). Qed.
Lemma lem7047274 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7047275 (f : nat -> nat) : (term58 f) = True.
Proof. exact (@lem7047274 (term17 f)). Qed.
Lemma lem7047276 (f : nat -> nat) : (term57 f) = True.
Proof. exact (TRANS (@lem7047272 f) (@lem7047275 f)). Qed.
Lemma lem7047277 (f : nat -> nat) : True = (term57 f).
Proof. exact (SYM (@lem7047276 f)). Qed.
Lemma lem7047278 (f : nat -> nat) : term57 f.
Proof. exact (EQ_MP (@lem7047277 f) (@lem0)). Qed.
Lemma lem7047279 (f : nat -> nat) : term56 f.
Proof. exact (@lem7047278 f (@lem7047128 f)). Qed.
