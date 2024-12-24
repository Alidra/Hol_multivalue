Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_FINITE_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_FINITE_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
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
Lemma lem7605777 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7605778 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (@lem7605777 (term1 A)). Qed.
Lemma lem7605779 {A : Type'} : (term2 A) = (term1 A).
Proof. exact (SYM (@lem7605778 A)). Qed.
Lemma lem7605780 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7605781 {A : Type'} : term4 A.
Proof. exact (@lem7605765 A). Qed.
Lemma lem7605783 {A : Type'} : term5 A.
Proof. exact (@lem3863773 (finite_image A)). Qed.
Lemma lem7605787 {_100044 A : Type'} (h1 : term6 _100044 A) : term6 _100044 A.
Proof. exact (h1). Qed.
Lemma lem7605788 {_100044 A : Type'} : term7 _100044 A.
Proof. exact (fun h0 : term6 _100044 A => @lem7605787 _100044 A h0). Qed.
Lemma lem7605789 {_100044 A : Type'} (h1 : term7 _100044 A) : term7 _100044 A.
Proof. exact (h1). Qed.
Lemma lem7605790 {_100044 A : Type'} (h1 : term6 _100044 A) : term6 _100044 A.
Proof. exact (h1). Qed.
Lemma lem7605791 {_100044 A : Type'} (h1 : term6 _100044 A) (h2 : term7 _100044 A) : term6 _100044 A.
Proof. exact (@lem7605789 _100044 A h2 (@lem7605790 _100044 A h1)). Qed.
Lemma lem7605792 {_100044 A : Type'} (h1 : term6 _100044 A) : term8 _100044 A.
Proof. exact (fun h0 : term7 _100044 A => @lem7605791 _100044 A h1 h0). Qed.
Lemma lem7605793 {_100044 A : Type'} (h1 : term7 _100044 A) : term7 _100044 A.
Proof. exact (h1). Qed.
Lemma lem7605794 {_100044 A : Type'} (h1 : term6 _100044 A) (h2 : term7 _100044 A) : term6 _100044 A.
Proof. exact (@lem7605792 _100044 A h1 (@lem7605793 _100044 A h2)). Qed.
Lemma lem7605795 {_100044 A : Type'} (h1 : term7 _100044 A) : term7 _100044 A.
Proof. exact (fun h0 : term6 _100044 A => @lem7605794 _100044 A h0 h1). Qed.
Lemma lem7605796 {_100044 A : Type'} : term9 _100044 A.
Proof. exact (fun h0 : term7 _100044 A => @lem7605795 _100044 A h0). Qed.
Lemma lem7605799 {_100044 A : Type'} : term7 _100044 A.
Proof. exact (@lem7605796 _100044 A (@lem7605788 _100044 A)). Qed.
Lemma lem7605800 {_100044 A : Type'} : term7 _100044 A.
Proof. exact (@lem7605799 _100044 A). Qed.
Lemma lem7605832 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7605833 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (@lem7605832 (term4 A)). Qed.
Lemma lem7605838 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (eq_refl (term12 A)). Qed.
Lemma lem7605839 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem7605838 A) (@lem7605833 A)). Qed.
Lemma lem7605842 {_100044 : Type'} : (term15 _100044) = (term15 _100044).
Proof. exact (eq_refl (term15 _100044)). Qed.
Lemma lem7605843 {_100044 A : Type'} : (term16 _100044 A) = (term17 _100044 A).
Proof. exact (MK_COMB (@lem7605842 _100044) (@lem7605839 A)). Qed.
Lemma lem7605846 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (eq_refl (term18 A)). Qed.
Lemma lem7605853 {_100044 A : Type'} : (term6 _100044 A) = (term19 _100044 A).
Proof. exact (MK_COMB (@lem7605846 A) (@lem7605843 _100044 A)). Qed.
Lemma lem7605854 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem7605855 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7605854 A s)). Qed.
Lemma lem7605856 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7605857 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem7605856 A) (@lem7605855 A)). Qed.
Lemma lem7605858 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7605859 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem7605858) (@lem7605857 A)). Qed.
Lemma lem7605868 {A : Type'} (s : type33 A) (n : nat) : ((@HAS_SIZE (finite_image A) s n) = (term22 A s n)) = ((@HAS_SIZE (finite_image A) s n) = (term22 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (finite_image A) s n) = (term22 A s n))). Qed.
Lemma lem7605869 {A : Type'} (s : type33 A) : (term23 A s) = (term23 A s).
Proof. exact (fun_ext (fun n : nat => @lem7605868 A s n)). Qed.
Lemma lem7605870 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7605871 {A : Type'} (s : type33 A) : (term24 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem7605870) (@lem7605869 A s)). Qed.
Lemma lem7605872 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7605871 A s)). Qed.
Lemma lem7605873 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7605874 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem7605873 A) (@lem7605872 A)). Qed.
Lemma lem7605875 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7605876 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7605875) (@lem7605874 A)). Qed.
Lemma lem7605877 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (MK_COMB (@lem7605876 A) (@lem7605859 A)). Qed.
Lemma lem7605886 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term26 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term26 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term26 _100044 s n))). Qed.
Lemma lem7605887 {_100044 : Type'} (s : _100044 -> Prop) : (term27 _100044 s) = (term27 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7605886 _100044 s n)). Qed.
Lemma lem7605888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7605889 {_100044 : Type'} (s : _100044 -> Prop) : (term28 _100044 s) = (term28 _100044 s).
Proof. exact (MK_COMB (@lem7605888) (@lem7605887 _100044 s)). Qed.
Lemma lem7605890 {_100044 : Type'} : (term29 _100044) = (term29 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7605889 _100044 s)). Qed.
Lemma lem7605891 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7605892 {_100044 : Type'} : (term30 _100044) = (term30 _100044).
Proof. exact (MK_COMB (@lem7605891 _100044) (@lem7605890 _100044)). Qed.
Lemma lem7605893 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7605894 {_100044 : Type'} : (term15 _100044) = (term15 _100044).
Proof. exact (MK_COMB (@lem7605893) (@lem7605892 _100044)). Qed.
Lemma lem7605895 {_100044 A : Type'} : (term17 _100044 A) = (term17 _100044 A).
Proof. exact (MK_COMB (@lem7605894 _100044) (@lem7605877 A)). Qed.
Lemma lem7605896 {A : Type'} (s : A -> Prop) : ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s)) = ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s)).
Proof. exact (eq_refl ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s))). Qed.
Lemma lem7605897 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7605896 A s)). Qed.
Lemma lem7605898 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7605899 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (MK_COMB (@lem7605898 A) (@lem7605897 A)). Qed.
Lemma lem7605900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7605901 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem7605900) (@lem7605899 A)). Qed.
Lemma lem7605902 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7605903 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem7605902) (@lem7605901 A)). Qed.
Lemma lem7605904 {_100044 A : Type'} : (term19 _100044 A) = (term19 _100044 A).
Proof. exact (MK_COMB (@lem7605903 A) (@lem7605895 _100044 A)). Qed.
Lemma lem7605953 {_100044 A : Type'} : (term6 _100044 A) = (term19 _100044 A).
Proof. exact (TRANS (@lem7605853 _100044 A) (@lem7605904 _100044 A)). Qed.
Lemma lem7605954 {_100044 A : Type'} : (term19 _100044 A) = (term6 _100044 A).
Proof. exact (SYM (@lem7605953 _100044 A)). Qed.
Lemma lem7605955 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7605957 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem7605958 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem7605960 {A : Type'} (P : type686 A) : (term32 A P) = (term33 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem7605961 {A : Type'} : (term3 A) = (term34 A).
Proof. exact (@lem7605960 A (term31 A)). Qed.
Lemma lem7605962 {A : Type'} (s : A -> Prop) : (term35 A s) = ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s)).
Proof. exact (eq_refl (term35 A s)). Qed.
Lemma lem7605963 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7605965 {A : Type'} (s : A -> Prop) : (term36 A s) = (term37 A s).
Proof. exact (MK_COMB (@lem7605963) (@lem7605962 A s)). Qed.
Lemma lem7605966 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7605965 A s)). Qed.
Lemma lem7605967 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7605968 {A : Type'} : (term34 A) = (term40 A).
Proof. exact (MK_COMB (@lem7605967 A) (@lem7605966 A)). Qed.
Lemma lem7605977 {A : Type'} : (term3 A) = (term40 A).
Proof. exact (TRANS (@lem7605961 A) (@lem7605968 A)). Qed.
Lemma lem7605978 {A : Type'} (h1 : term3 A) : term40 A.
Proof. exact (EQ_MP (@lem7605977 A) (@lem7605955 A h1)). Qed.
Lemma lem7606286 {A : Type'} (s : type33 A) (n : nat) : (term41 A s n) = (term42 A s n).
Proof. exact (@lem17045 (@FINITE (finite_image A) s) ((@CARD (finite_image A) s) = n)). Qed.
Lemma lem7606292 {A : Type'} (s : type33 A) (n : nat) : (term43 A s n) = (term43 A s n).
Proof. exact (eq_refl (term43 A s n)). Qed.
Lemma lem7606294 {A : Type'} (s : type33 A) (n : nat) : (term44 A s n) = (term44 A s n).
Proof. exact (eq_refl (term44 A s n)). Qed.
Lemma lem7606295 {A : Type'} (s : type33 A) (n : nat) : (term45 A s n) = (term46 A s n).
Proof. exact (MK_COMB (@lem7606294 A s n) (@lem7606286 A s n)). Qed.
Lemma lem7606296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7606297 {A : Type'} (s : type33 A) (n : nat) : (term47 A s n) = (term48 A s n).
Proof. exact (MK_COMB (@lem7606296) (@lem7606295 A s n)). Qed.
Lemma lem7606298 {A : Type'} (s : type33 A) (n : nat) : (term49 A s n) = (term50 A s n).
Proof. exact (MK_COMB (@lem7606297 A s n) (@lem7606292 A s n)). Qed.
Lemma lem7606299 {A : Type'} (s : type33 A) (n : nat) : ((@HAS_SIZE (finite_image A) s n) = (term22 A s n)) = (term49 A s n).
Proof. exact (@lem17784 (@HAS_SIZE (finite_image A) s n) (term22 A s n)). Qed.
Lemma lem7606300 {A : Type'} (s : type33 A) (n : nat) : ((@HAS_SIZE (finite_image A) s n) = (term22 A s n)) = (term50 A s n).
Proof. exact (TRANS (@lem7606299 A s n) (@lem7606298 A s n)). Qed.
Lemma lem7606301 {A : Type'} (s : type33 A) : (term23 A s) = (term51 A s).
Proof. exact (fun_ext (fun n : nat => @lem7606300 A s n)). Qed.
Lemma lem7606302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7606303 {A : Type'} (s : type33 A) : (term24 A s) = (term52 A s).
Proof. exact (MK_COMB (@lem7606302) (@lem7606301 A s)). Qed.
Lemma lem7606304 {A : Type'} : (term25 A) = (term53 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7606303 A s)). Qed.
Lemma lem7606305 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7606306 {A : Type'} : (term5 A) = (term54 A).
Proof. exact (MK_COMB (@lem7606305 A) (@lem7606304 A)). Qed.
Lemma lem7606312 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7606313 (P : nat -> Prop) (Q : nat -> Prop) : (term57 P Q) = (term58 P Q).
Proof. exact (@lem7606312 nat P Q). Qed.
Lemma lem7606314 {A : Type'} (s : type33 A) : (term59 A s) = (term60 A s).
Proof. exact (@lem7606313 (term61 A s) (term62 A s)). Qed.
Lemma lem7606315 {A : Type'} (s : type33 A) (n : nat) : (term63 A s n) = (term46 A s n).
Proof. exact (eq_refl (term63 A s n)). Qed.
Lemma lem7606316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7606317 {A : Type'} (s : type33 A) (n : nat) : (term64 A s n) = (term48 A s n).
Proof. exact (MK_COMB (@lem7606316) (@lem7606315 A s n)). Qed.
Lemma lem7606318 {A : Type'} (s : type33 A) (n : nat) : (term65 A s n) = (term43 A s n).
Proof. exact (eq_refl (term65 A s n)). Qed.
Lemma lem7606319 {A : Type'} (s : type33 A) (n : nat) : (term66 A s n) = (term50 A s n).
Proof. exact (MK_COMB (@lem7606317 A s n) (@lem7606318 A s n)). Qed.
Lemma lem7606320 {A : Type'} (s : type33 A) : (term67 A s) = (term51 A s).
Proof. exact (fun_ext (fun n : nat => @lem7606319 A s n)). Qed.
Lemma lem7606321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7606322 {A : Type'} (s : type33 A) : (term59 A s) = (term52 A s).
Proof. exact (MK_COMB (@lem7606321) (@lem7606320 A s)). Qed.
Lemma lem7606323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7606324 {A : Type'} (s : type33 A) : (term68 A s) = (term69 A s).
Proof. exact (MK_COMB (@lem7606323) (@lem7606322 A s)). Qed.
Lemma lem7606325 {A : Type'} (s : type33 A) (n : nat) : (term63 A s n) = (term46 A s n).
Proof. exact (eq_refl (term63 A s n)). Qed.
Lemma lem7606326 {A : Type'} (s : type33 A) : (term70 A s) = (term61 A s).
Proof. exact (fun_ext (fun n : nat => @lem7606325 A s n)). Qed.
Lemma lem7606327 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7606328 {A : Type'} (s : type33 A) : (term71 A s) = (term72 A s).
Proof. exact (MK_COMB (@lem7606327) (@lem7606326 A s)). Qed.
Lemma lem7606329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7606330 {A : Type'} (s : type33 A) : (term73 A s) = (term74 A s).
Proof. exact (MK_COMB (@lem7606329) (@lem7606328 A s)). Qed.
Lemma lem7606331 {A : Type'} (s : type33 A) (n : nat) : (term65 A s n) = (term43 A s n).
Proof. exact (eq_refl (term65 A s n)). Qed.
Lemma lem7606332 {A : Type'} (s : type33 A) : (term75 A s) = (term62 A s).
Proof. exact (fun_ext (fun n : nat => @lem7606331 A s n)). Qed.
Lemma lem7606333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7606334 {A : Type'} (s : type33 A) : (term76 A s) = (term77 A s).
Proof. exact (MK_COMB (@lem7606333) (@lem7606332 A s)). Qed.
Lemma lem7606335 {A : Type'} (s : type33 A) : (term60 A s) = (term78 A s).
Proof. exact (MK_COMB (@lem7606330 A s) (@lem7606334 A s)). Qed.
Lemma lem7606336 {A : Type'} (s : type33 A) : ((term59 A s) = (term60 A s)) = ((term52 A s) = (term78 A s)).
Proof. exact (MK_COMB (@lem7606324 A s) (@lem7606335 A s)). Qed.
Lemma lem7606337 {A : Type'} (s : type33 A) : (term52 A s) = (term78 A s).
Proof. exact (EQ_MP (@lem7606336 A s) (@lem7606314 A s)). Qed.
Lemma lem7606434 {A : Type'} : (term53 A) = (term79 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7606337 A s)). Qed.
Lemma lem7606435 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7606436 {A : Type'} : (term54 A) = (term80 A).
Proof. exact (MK_COMB (@lem7606435 A) (@lem7606434 A)). Qed.
Lemma lem7606438 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7606439 {A : Type'} (P : type59 A) (Q : type59 A) : (term81 A P Q) = (term82 A P Q).
Proof. exact (@lem7606438 (type33 A) P Q). Qed.
Lemma lem7606440 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (@lem7606439 A (term85 A) (term86 A)). Qed.
Lemma lem7606441 {A : Type'} (s : type33 A) : (term87 A s) = (term72 A s).
Proof. exact (eq_refl (term87 A s)). Qed.
Lemma lem7606442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7606443 {A : Type'} (s : type33 A) : (term88 A s) = (term74 A s).
Proof. exact (MK_COMB (@lem7606442) (@lem7606441 A s)). Qed.
Lemma lem7606444 {A : Type'} (s : type33 A) : (term89 A s) = (term77 A s).
Proof. exact (eq_refl (term89 A s)). Qed.
Lemma lem7606445 {A : Type'} (s : type33 A) : (term90 A s) = (term78 A s).
Proof. exact (MK_COMB (@lem7606443 A s) (@lem7606444 A s)). Qed.
Lemma lem7606446 {A : Type'} : (term91 A) = (term79 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7606445 A s)). Qed.
Lemma lem7606447 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7606448 {A : Type'} : (term83 A) = (term80 A).
Proof. exact (MK_COMB (@lem7606447 A) (@lem7606446 A)). Qed.
Lemma lem7606449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7606450 {A : Type'} : (term92 A) = (term93 A).
Proof. exact (MK_COMB (@lem7606449) (@lem7606448 A)). Qed.
Lemma lem7606451 {A : Type'} (s : type33 A) : (term87 A s) = (term72 A s).
Proof. exact (eq_refl (term87 A s)). Qed.
Lemma lem7606452 {A : Type'} : (term94 A) = (term85 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7606451 A s)). Qed.
Lemma lem7606453 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7606454 {A : Type'} : (term95 A) = (term96 A).
Proof. exact (MK_COMB (@lem7606453 A) (@lem7606452 A)). Qed.
Lemma lem7606455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7606456 {A : Type'} : (term97 A) = (term98 A).
Proof. exact (MK_COMB (@lem7606455) (@lem7606454 A)). Qed.
Lemma lem7606457 {A : Type'} (s : type33 A) : (term89 A s) = (term77 A s).
Proof. exact (eq_refl (term89 A s)). Qed.
Lemma lem7606458 {A : Type'} : (term99 A) = (term86 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7606457 A s)). Qed.
Lemma lem7606459 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7606460 {A : Type'} : (term100 A) = (term101 A).
Proof. exact (MK_COMB (@lem7606459 A) (@lem7606458 A)). Qed.
Lemma lem7606461 {A : Type'} : (term84 A) = (term102 A).
Proof. exact (MK_COMB (@lem7606456 A) (@lem7606460 A)). Qed.
Lemma lem7606462 {A : Type'} : ((term83 A) = (term84 A)) = ((term80 A) = (term102 A)).
Proof. exact (MK_COMB (@lem7606450 A) (@lem7606461 A)). Qed.
Lemma lem7606463 {A : Type'} : (term80 A) = (term102 A).
Proof. exact (EQ_MP (@lem7606462 A) (@lem7606440 A)). Qed.
Lemma lem7606570 {A : Type'} : (term54 A) = (term102 A).
Proof. exact (TRANS (@lem7606436 A) (@lem7606463 A)). Qed.
Lemma lem7606571 {A : Type'} : (term5 A) = (term102 A).
Proof. exact (TRANS (@lem7606306 A) (@lem7606570 A)). Qed.
Lemma lem7606572 {A : Type'} (h1 : term5 A) : term102 A.
Proof. exact (EQ_MP (@lem7606571 A) (@lem7605957 A h1)). Qed.
Lemma lem7606573 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem7606574 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7606573 A s)). Qed.
Lemma lem7606575 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7606584 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem7606575 A) (@lem7606574 A)). Qed.
Lemma lem7606585 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (EQ_MP (@lem7606584 A) (@lem7605958 A h1)). Qed.
Lemma lem7606673 {A : Type'} (s : type33 A) (n : nat) : (term43 A s n) = (term43 A s n).
Proof. exact (eq_refl (term43 A s n)). Qed.
Lemma lem7606674 {A : Type'} (s : type33 A) : (term62 A s) = (term62 A s).
Proof. exact (fun_ext (fun n : nat => @lem7606673 A s n)). Qed.
Lemma lem7606675 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7606676 {A : Type'} (s : type33 A) : (term77 A s) = (term77 A s).
Proof. exact (MK_COMB (@lem7606675) (@lem7606674 A s)). Qed.
Lemma lem7606677 {A : Type'} : (term86 A) = (term86 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7606676 A s)). Qed.
Lemma lem7606678 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7606679 {A : Type'} : (term101 A) = (term101 A).
Proof. exact (MK_COMB (@lem7606678 A) (@lem7606677 A)). Qed.
Lemma lem7606704 {A : Type'} (s : type33 A) (n : nat) : (term46 A s n) = (term46 A s n).
Proof. exact (eq_refl (term46 A s n)). Qed.
Lemma lem7606705 {A : Type'} (s : type33 A) : (term61 A s) = (term61 A s).
Proof. exact (fun_ext (fun n : nat => @lem7606704 A s n)). Qed.
Lemma lem7606706 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7606707 {A : Type'} (s : type33 A) : (term72 A s) = (term72 A s).
Proof. exact (MK_COMB (@lem7606706) (@lem7606705 A s)). Qed.
Lemma lem7606708 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7606707 A s)). Qed.
Lemma lem7606709 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7606710 {A : Type'} : (term96 A) = (term96 A).
Proof. exact (MK_COMB (@lem7606709 A) (@lem7606708 A)). Qed.
Lemma lem7606711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7606712 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7606711) (@lem7606710 A)). Qed.
Lemma lem7606713 {A : Type'} : (term102 A) = (term102 A).
Proof. exact (MK_COMB (@lem7606712 A) (@lem7606679 A)). Qed.
Lemma lem7606714 {A : Type'} (h1 : term5 A) : term102 A.
Proof. exact (EQ_MP (@lem7606713 A) (@lem7606572 A h1)). Qed.
Lemma lem7606721 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem7606722 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7606721 A s)). Qed.
Lemma lem7606723 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7606724 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem7606723 A) (@lem7606722 A)). Qed.
Lemma lem7606725 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (EQ_MP (@lem7606724 A) (@lem7606585 A h1)). Qed.
Lemma lem7606737 {A : Type'} (s : A -> Prop) (h1 : term37 A s) : term37 A s.
Proof. exact (h1). Qed.
Lemma lem7606738 {A : Type'} (h1 : term5 A) : term101 A.
Proof. exact (proj2 (@lem7606714 A h1)). Qed.
Lemma lem7606743 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem7606744 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7606743 A s)). Qed.
Lemma lem7606745 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7606747 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem7606745 A) (@lem7606744 A)). Qed.
Lemma lem7606748 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (EQ_MP (@lem7606747 A) (@lem7606725 A h1)). Qed.
Lemma lem7606752 {A : Type'} (s : A -> Prop) (h1 : term37 A s) : term37 A s.
Proof. exact (h1). Qed.
Lemma lem7606792 {A : Type'} (s : type33 A) (n : nat) : (term43 A s n) = (term103 A s n).
Proof. exact (@lem19490 (@FINITE (finite_image A) s) (term104 A s n) ((@CARD (finite_image A) s) = n)). Qed.
Lemma lem7606793 {A : Type'} (s : type33 A) : (term62 A s) = (term105 A s).
Proof. exact (fun_ext (fun n : nat => @lem7606792 A s n)). Qed.
Lemma lem7606794 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7606795 {A : Type'} (s : type33 A) : (term77 A s) = (term106 A s).
Proof. exact (MK_COMB (@lem7606794) (@lem7606793 A s)). Qed.
Lemma lem7606796 {A : Type'} : (term86 A) = (term107 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7606795 A s)). Qed.
Lemma lem7606797 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7606799 {A : Type'} : (term101 A) = (term108 A).
Proof. exact (MK_COMB (@lem7606797 A) (@lem7606796 A)). Qed.
Lemma lem7606800 {A : Type'} (h1 : term5 A) : term108 A.
Proof. exact (EQ_MP (@lem7606799 A) (@lem7606738 A h1)). Qed.
Lemma lem7606849 {A : Type'} (_97809 : A -> Prop) (h1 : term4 A) : term109 A _97809.
Proof. exact (@lem7606748 A h1 _97809). Qed.
Lemma lem7606850 {A : Type'} (_97809 : A -> Prop) : (term109 A _97809) = (term20 A _97809).
Proof. exact (eq_refl (term109 A _97809)). Qed.
Lemma lem7606858 {A : Type'} (_97812 : type33 A) (h1 : term5 A) : term110 A _97812.
Proof. exact (@lem7606800 A h1 _97812). Qed.
Lemma lem7606859 {A : Type'} (_97812 : type33 A) : (term110 A _97812) = (term106 A _97812).
Proof. exact (eq_refl (term110 A _97812)). Qed.
Lemma lem7606860 {A : Type'} (_97812 : type33 A) (h1 : term5 A) : term106 A _97812.
Proof. exact (EQ_MP (@lem7606859 A _97812) (@lem7606858 A _97812 h1)). Qed.
Lemma lem7606861 {A : Type'} (_97812 : type33 A) (_97813 : nat) (h1 : term5 A) : term111 A _97812 _97813.
Proof. exact (@lem7606860 A _97812 h1 _97813). Qed.
Lemma lem7606862 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term111 A _97812 _97813) = (term103 A _97812 _97813).
Proof. exact (eq_refl (term111 A _97812 _97813)). Qed.
Lemma lem7606863 {A : Type'} (_97812 : type33 A) (_97813 : nat) (h1 : term5 A) : term103 A _97812 _97813.
Proof. exact (EQ_MP (@lem7606862 A _97812 _97813) (@lem7606861 A _97812 _97813 h1)). Qed.
Lemma lem7606883 {A : Type'} (s : A -> Prop) (h1 : term37 A s) : term37 A s.
Proof. exact (h1). Qed.
Lemma lem7606927 {A : Type'} (_97812 : type33 A) (_97813 : nat) (h1 : term5 A) : term112 A _97812 _97813.
Proof. exact (proj2 (@lem7606863 A _97812 _97813 h1)). Qed.
Lemma lem7607023 {A : Type'} (_97809 : A -> Prop) (h1 : term4 A) : term20 A _97809.
Proof. exact (EQ_MP (@lem7606850 A _97809) (@lem7606849 A _97809 h1)). Qed.
Lemma lem7607024 {A : Type'} (_97809 : A -> Prop) (h1 : term4 A) : term20 A _97809.
Proof. exact (@lem7607023 A _97809 h1). Qed.
Lemma lem7607025 {A : Type'} (s : A -> Prop) (h1 : term4 A) : term20 A s.
Proof. exact (@lem7607024 A s h1). Qed.
Lemma lem7607026 {A : Type'} (s : A -> Prop) (h1 : term4 A) : term113 A s.
Proof. exact (fun h0 : term114 A s => @lem7607025 A s h1). Qed.
Lemma lem7607028 (p : Prop) : (term115 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7607029 {A : Type'} (s : A -> Prop) : (term113 A s) = (term20 A s).
Proof. exact (@lem7607028 (term20 A s)). Qed.
Lemma lem7607030 {A : Type'} (s : A -> Prop) (h1 : term4 A) : term20 A s.
Proof. exact (EQ_MP (@lem7607029 A s) (@lem7607026 A s h1)). Qed.
Lemma lem7607036 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7607037 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term112 A _97812 _97813) = (term116 A _97812 _97813).
Proof. exact (@lem7607036 ((@CARD (finite_image A) _97812) = _97813) (term104 A _97812 _97813)). Qed.
Lemma lem7607045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7607046 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term117 A _97812 _97813) = (term118 A _97812 _97813).
Proof. exact (MK_COMB (@lem7607045) (@lem7607037 A _97812 _97813)). Qed.
Lemma lem7607054 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term116 A _97812 _97813) = (term116 A _97812 _97813).
Proof. exact (eq_refl (term116 A _97812 _97813)). Qed.
Lemma lem7607055 {A : Type'} (_97812 : type33 A) (_97813 : nat) : ((term112 A _97812 _97813) = (term116 A _97812 _97813)) = ((term116 A _97812 _97813) = (term116 A _97812 _97813)).
Proof. exact (MK_COMB (@lem7607046 A _97812 _97813) (@lem7607054 A _97812 _97813)). Qed.
Lemma lem7607057 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7607058 (x : Prop) : (x = x) = True.
Proof. exact (@lem7607057 Prop x). Qed.
Lemma lem7607059 {A : Type'} (_97812 : type33 A) (_97813 : nat) : ((term116 A _97812 _97813) = (term116 A _97812 _97813)) = True.
Proof. exact (@lem7607058 (term116 A _97812 _97813)). Qed.
Lemma lem7607060 {A : Type'} (_97812 : type33 A) (_97813 : nat) : ((term112 A _97812 _97813) = (term116 A _97812 _97813)) = True.
Proof. exact (TRANS (@lem7607055 A _97812 _97813) (@lem7607059 A _97812 _97813)). Qed.
Lemma lem7607061 {A : Type'} (_97812 : type33 A) (_97813 : nat) : True = ((term112 A _97812 _97813) = (term116 A _97812 _97813)).
Proof. exact (SYM (@lem7607060 A _97812 _97813)). Qed.
Lemma lem7607062 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term112 A _97812 _97813) = (term116 A _97812 _97813).
Proof. exact (EQ_MP (@lem7607061 A _97812 _97813) (@lem0)). Qed.
Lemma lem7607063 {A : Type'} (_97812 : type33 A) (_97813 : nat) (h1 : term5 A) : term116 A _97812 _97813.
Proof. exact (EQ_MP (@lem7607062 A _97812 _97813) (@lem7606927 A _97812 _97813 h1)). Qed.
Lemma lem7607065 (b : Prop) (a : Prop) : (a \/ b) = (term119 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7607066 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term116 A _97812 _97813) = (term120 A _97812 _97813).
Proof. exact (@lem7607065 (term104 A _97812 _97813) ((@CARD (finite_image A) _97812) = _97813)). Qed.
Lemma lem7607068 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7607069 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term122 A _97812 _97813) = (@HAS_SIZE (finite_image A) _97812 _97813).
Proof. exact (@lem7607068 (@HAS_SIZE (finite_image A) _97812 _97813)). Qed.
Lemma lem7607070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7607071 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term123 A _97812 _97813) = (term124 A _97812 _97813).
Proof. exact (MK_COMB (@lem7607070) (@lem7607069 A _97812 _97813)). Qed.
Lemma lem7607072 {A : Type'} (_97812 : type33 A) (_97813 : nat) : ((@CARD (finite_image A) _97812) = _97813) = ((@CARD (finite_image A) _97812) = _97813).
Proof. exact (eq_refl ((@CARD (finite_image A) _97812) = _97813)). Qed.
Lemma lem7607073 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term120 A _97812 _97813) = (term125 A _97812 _97813).
Proof. exact (MK_COMB (@lem7607071 A _97812 _97813) (@lem7607072 A _97812 _97813)). Qed.
Lemma lem7607074 {A : Type'} (_97812 : type33 A) (_97813 : nat) : (term116 A _97812 _97813) = (term125 A _97812 _97813).
Proof. exact (TRANS (@lem7607066 A _97812 _97813) (@lem7607073 A _97812 _97813)). Qed.
Lemma lem7607077 {A : Type'} (_97812 : type33 A) (_97813 : nat) (h1 : term5 A) : term125 A _97812 _97813.
Proof. exact (EQ_MP (@lem7607074 A _97812 _97813) (@lem7607063 A _97812 _97813 h1)). Qed.
Lemma lem7607078 {A : Type'} (_97812 : type33 A) (_97813 : nat) (h1 : term5 A) : term125 A _97812 _97813.
Proof. exact (@lem7607077 A _97812 _97813 h1). Qed.
Lemma lem7607079 {A : Type'} (s : A -> Prop) (h1 : term5 A) : term126 A s.
Proof. exact (@lem7607078 A (@UNIV (finite_image A)) (@dimindex A s) h1). Qed.
Lemma lem7607082 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s).
Proof. exact (@lem7607079 A s h2 (@lem7607030 A s h1)). Qed.
Lemma lem7607083 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s).
Proof. exact (@lem7607082 A s h1 h2). Qed.
Lemma lem7607084 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) : term127 A s.
Proof. exact (fun h0 : term37 A s => @lem7607083 A s h1 h2). Qed.
Lemma lem7607086 (p : Prop) : (term115 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7607087 {A : Type'} (s : A -> Prop) : (term127 A s) = ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s)).
Proof. exact (@lem7607086 ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s))). Qed.
Lemma lem7607088 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s).
Proof. exact (EQ_MP (@lem7607087 A s) (@lem7607084 A s h1 h2)). Qed.
Lemma lem7607091 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7607093 {A : Type'} (s : A -> Prop) : (term37 A s) = (term128 A s).
Proof. exact (@lem7607091 ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A s))). Qed.
Lemma lem7607096 {A : Type'} (s : A -> Prop) (h1 : term37 A s) : term128 A s.
Proof. exact (EQ_MP (@lem7607093 A s) (@lem7606883 A s h1)). Qed.
Lemma lem7607099 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : False.
Proof. exact (@lem7607096 A s h3 (@lem7607088 A s h1 h2)). Qed.
Lemma lem7607100 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : term129.
Proof. exact (fun h0 : ~ False => @lem7607099 A s h1 h2 h3). Qed.
Lemma lem7607102 (p : Prop) : (term115 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7607103 : term129 = False.
Proof. exact (@lem7607102 False). Qed.
Lemma lem7607104 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : False.
Proof. exact (EQ_MP (@lem7607103) (@lem7607100 A s h1 h2 h3)). Qed.
Lemma lem7607105 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : (term37 A s) = False.
Proof. exact (prop_ext (fun h4 : term37 A s => @lem7607104 A s h1 h2 h3) (fun h4 : False => @lem7606883 A s h3)). Qed.
Lemma lem7607106 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : False.
Proof. exact (EQ_MP (@lem7607105 A s h1 h2 h3) (@lem7606883 A s h3)). Qed.
Lemma lem7607107 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : (term37 A s) = False.
Proof. exact (prop_ext (fun h4 : term37 A s => @lem7607106 A s h1 h2 h3) (fun h4 : False => @lem7606752 A s h3)). Qed.
Lemma lem7607108 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : False.
Proof. exact (EQ_MP (@lem7607107 A s h1 h2 h3) (@lem7606752 A s h3)). Qed.
Lemma lem7607109 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : (term37 A s) = False.
Proof. exact (prop_ext (fun h4 : term37 A s => @lem7607108 A s h1 h2 h3) (fun h4 : False => @lem7606752 A s h3)). Qed.
Lemma lem7607110 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : False.
Proof. exact (EQ_MP (@lem7607109 A s h1 h2 h3) (@lem7606752 A s h3)). Qed.
Lemma lem7607111 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : (term4 A) = False.
Proof. exact (prop_ext (fun h4 : term4 A => @lem7607110 A s h1 h2 h3) (fun h4 : False => @lem7606748 A h1)). Qed.
Lemma lem7607112 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : False.
Proof. exact (EQ_MP (@lem7607111 A s h1 h2 h3) (@lem7606748 A h1)). Qed.
Lemma lem7607113 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : (term37 A s) = False.
Proof. exact (prop_ext (fun h4 : term37 A s => @lem7607112 A s h1 h2 h3) (fun h4 : False => @lem7606737 A s h3)). Qed.
Lemma lem7607114 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : False.
Proof. exact (EQ_MP (@lem7607113 A s h1 h2 h3) (@lem7606737 A s h3)). Qed.
Lemma lem7607115 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : (term4 A) = False.
Proof. exact (prop_ext (fun h4 : term4 A => @lem7607114 A s h1 h2 h3) (fun h4 : False => @lem7606725 A h1)). Qed.
Lemma lem7607116 {A : Type'} (s : A -> Prop) (h1 : term4 A) (h2 : term5 A) (h3 : term37 A s) : False.
Proof. exact (EQ_MP (@lem7607115 A s h1 h2 h3) (@lem7606725 A h1)). Qed.
Lemma lem7607117 {A : Type'} (h1 : term4 A) (h2 : term5 A) (h3 : term3 A) : False.
Proof. exact (ex_elim (@lem7605978 A h3) (fun s : A -> Prop => fun h0 : term39 A s => @lem7607116 A s h1 h2 h0)). Qed.
Lemma lem7607118 {A : Type'} (h1 : term4 A) (h2 : term5 A) (h3 : term3 A) : (term4 A) = False.
Proof. exact (prop_ext (fun h4 : term4 A => @lem7607117 A h1 h2 h3) (fun h4 : False => @lem7606585 A h1)). Qed.
Lemma lem7607119 {A : Type'} (h1 : term4 A) (h2 : term5 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7607118 A h1 h2 h3) (@lem7606585 A h1)). Qed.
Lemma lem7607120 {A : Type'} (h1 : term5 A) (h2 : term3 A) : term10 A.
Proof. exact (fun h0 : term4 A => @lem7607119 A h0 h1 h2). Qed.
Lemma lem7607121 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem7607122 {A : Type'} (h1 : term5 A) (h2 : term3 A) : term11 A.
Proof. exact (EQ_MP (@lem7607121 A) (@lem7607120 A h1 h2)). Qed.
Lemma lem7607123 {A : Type'} (h1 : term3 A) : term14 A.
Proof. exact (fun h0 : term5 A => @lem7607122 A h0 h1). Qed.
Lemma lem7607124 {_100044 A : Type'} (h1 : term3 A) : term17 _100044 A.
Proof. exact (fun h0 : term30 _100044 => @lem7607123 A h1). Qed.
Lemma lem7607125 {_100044 A : Type'} : term19 _100044 A.
Proof. exact (fun h0 : term3 A => @lem7607124 _100044 A h0). Qed.
Lemma lem7607126 {_100044 A : Type'} : term6 _100044 A.
Proof. exact (EQ_MP (@lem7605954 _100044 A) (@lem7607125 _100044 A)). Qed.
Lemma lem7607128 {_100044 A : Type'} : term6 _100044 A.
Proof. exact (@lem7605800 _100044 A (@lem7607126 _100044 A)). Qed.
Lemma lem7607129 {_100044 A : Type'} (h1 : term3 A) : term16 _100044 A.
Proof. exact (@lem7607128 _100044 A (@lem7605780 A h1)). Qed.
Lemma lem7607130 {A : Type'} (h1 : term3 A) : term13 A.
Proof. exact (@lem7607129 Prop A h1 (@lem3863773 Prop)). Qed.
Lemma lem7607131 {A : Type'} (h1 : term3 A) : term10 A.
Proof. exact (@lem7607130 A h1 (@lem7605783 A)). Qed.
Lemma lem7607132 {A : Type'} (h1 : term3 A) : False.
Proof. exact (@lem7607131 A h1 (@lem7605781 A)). Qed.
Lemma lem7607133 {A : Type'} (h1 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h2 : term3 A => @lem7607132 A h1) (fun h2 : False => @lem7605780 A h1)). Qed.
Lemma lem7607134 {A : Type'} (h1 : term3 A) : False.
Proof. exact (EQ_MP (@lem7607133 A h1) (@lem7605780 A h1)). Qed.
Lemma lem7607135 {A : Type'} : term2 A.
Proof. exact (fun h0 : term3 A => @lem7607134 A h0). Qed.
Lemma lem7607136 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem7605779 A) (@lem7607135 A)). Qed.
