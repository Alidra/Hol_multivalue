Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_IN_IMAGE_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import IN_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3386921 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3386922 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3386923 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3386922 t1) (@lem3386921 t1)). Qed.
Lemma lem3386924 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3386923 t1 t2). Qed.
Lemma lem3386925 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3386926 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3386925 t1 t2) (@lem3386924 t1 t2)). Qed.
Lemma lem3386927 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3386926 t1 t2 t3). Qed.
Lemma lem3386928 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3386929 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3386928 t1 t2 t3) (@lem3386927 t1 t2 t3)). Qed.
Lemma lem3386930 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3386929 t1 t2 t3)). Qed.
Lemma lem3386931 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3386932 {A B : Type'} (y : B) : (term7 A B y) = (term8 A B y).
Proof. exact (eq_refl (term7 A B y)). Qed.
Lemma lem3386933 {A B : Type'} (y : B) : term8 A B y.
Proof. exact (EQ_MP (@lem3386932 A B y) (@lem3386931 A B y)). Qed.
Lemma lem3386934 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (@lem3386933 A B y s). Qed.
Lemma lem3386935 {A B : Type'} (y : B) (s : A -> Prop) : (term9 A B y s) = (term10 A B y s).
Proof. exact (eq_refl (term9 A B y s)). Qed.
Lemma lem3386936 {A B : Type'} (y : B) (s : A -> Prop) : term10 A B y s.
Proof. exact (EQ_MP (@lem3386935 A B y s) (@lem3386934 A B y s)). Qed.
Lemma lem3386937 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term11 A B y s f.
Proof. exact (@lem3386936 A B y s f). Qed.
Lemma lem3386938 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y s f) = ((term12 A B y f s) = (term13 A B y f s)).
Proof. exact (eq_refl (term11 A B y s f)). Qed.
Lemma lem3386957 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem3386938 A B y f s) (@lem3386937 A B y s f)). Qed.
Lemma lem3386958 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term14 _88003 _88004 y f s) = (term15 _88003 _88004 y f s).
Proof. exact (@lem3386957 _88004 _88003 y f s). Qed.
Lemma lem3386967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386968 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term16 _88003 _88004 y f s) = (term17 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3386967) (@lem3386958 _88003 _88004 y f s)). Qed.
Lemma lem3386969 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3386970 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term18 _88003 _88004 f s P y) = (term19 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3386968 _88003 _88004 y f s) (@lem3386969 _88003 P y)). Qed.
Lemma lem3386973 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term20 _88003 _88004 f s P) = (term21 _88003 _88004 f s P).
Proof. exact (fun_ext (fun y : _88003 => @lem3386970 _88003 _88004 f s P y)). Qed.
Lemma lem3386974 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3386975 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term22 _88003 _88004 f s P) = (term23 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3386974 _88003) (@lem3386973 _88003 _88004 f s P)). Qed.
Lemma lem3386980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386981 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term24 _88003 _88004 f s P) = (term25 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3386980) (@lem3386975 _88003 _88004 f s P)). Qed.
Lemma lem3386988 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term26 _88003 _88004 s P f) = (term26 _88003 _88004 s P f).
Proof. exact (eq_refl (term26 _88003 _88004 s P f)). Qed.
Lemma lem3386989 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : ((term22 _88003 _88004 f s P) = (term26 _88003 _88004 s P f)) = ((term23 _88003 _88004 f s P) = (term26 _88003 _88004 s P f)).
Proof. exact (MK_COMB (@lem3386981 _88003 _88004 f s P) (@lem3386988 _88003 _88004 s P f)). Qed.
Lemma lem3386992 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) : (term27 _88003 _88004 P f) = (term28 _88003 _88004 P f).
Proof. exact (fun_ext (fun s : _88004 -> Prop => @lem3386989 _88003 _88004 s P f)). Qed.
Lemma lem3386993 {_88004 : Type'} : (@all (_88004 -> Prop)) = (@all (_88004 -> Prop)).
Proof. exact (eq_refl (@all (_88004 -> Prop))). Qed.
Lemma lem3386994 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) : (term29 _88003 _88004 P f) = (term30 _88003 _88004 P f).
Proof. exact (MK_COMB (@lem3386993 _88004) (@lem3386992 _88003 _88004 P f)). Qed.
Lemma lem3386999 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term31 _88003 _88004 P) = (term32 _88003 _88004 P).
Proof. exact (fun_ext (fun f : _88004 -> _88003 => @lem3386994 _88003 _88004 P f)). Qed.
Lemma lem3387000 {_88003 _88004 : Type'} : (@all (_88004 -> _88003)) = (@all (_88004 -> _88003)).
Proof. exact (eq_refl (@all (_88004 -> _88003))). Qed.
Lemma lem3387001 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term33 _88003 _88004 P) = (term34 _88003 _88004 P).
Proof. exact (MK_COMB (@lem3387000 _88003 _88004) (@lem3386999 _88003 _88004 P)). Qed.
Lemma lem3387006 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term34 _88003 _88004 P) = (term33 _88003 _88004 P).
Proof. exact (SYM (@lem3387001 _88003 _88004 P)). Qed.
Lemma lem3387008 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3387009 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term34 _88003 _88004 P) = (term36 _88003 _88004 P).
Proof. exact (@lem3387008 (term34 _88003 _88004 P)). Qed.
Lemma lem3387010 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term36 _88003 _88004 P) = (term34 _88003 _88004 P).
Proof. exact (SYM (@lem3387009 _88003 _88004 P)). Qed.
Lemma lem3387011 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term37 _88003 _88004 P) : term37 _88003 _88004 P.
Proof. exact (h1). Qed.
Lemma lem3387014 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term36 _88003 _88004 P) : term36 _88003 _88004 P.
Proof. exact (h1). Qed.
Lemma lem3387015 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term38 _88003 _88004 P.
Proof. exact (fun h0 : term36 _88003 _88004 P => @lem3387014 _88003 _88004 P h0). Qed.
Lemma lem3387016 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term38 _88003 _88004 P) : term38 _88003 _88004 P.
Proof. exact (h1). Qed.
Lemma lem3387017 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term36 _88003 _88004 P) : term36 _88003 _88004 P.
Proof. exact (h1). Qed.
Lemma lem3387018 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term36 _88003 _88004 P) (h2 : term38 _88003 _88004 P) : term36 _88003 _88004 P.
Proof. exact (@lem3387016 _88003 _88004 P h2 (@lem3387017 _88003 _88004 P h1)). Qed.
Lemma lem3387019 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term36 _88003 _88004 P) : term39 _88003 _88004 P.
Proof. exact (fun h0 : term38 _88003 _88004 P => @lem3387018 _88003 _88004 P h1 h0). Qed.
Lemma lem3387020 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term38 _88003 _88004 P) : term38 _88003 _88004 P.
Proof. exact (h1). Qed.
Lemma lem3387021 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term36 _88003 _88004 P) (h2 : term38 _88003 _88004 P) : term36 _88003 _88004 P.
Proof. exact (@lem3387019 _88003 _88004 P h1 (@lem3387020 _88003 _88004 P h2)). Qed.
Lemma lem3387022 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term38 _88003 _88004 P) : term38 _88003 _88004 P.
Proof. exact (fun h0 : term36 _88003 _88004 P => @lem3387021 _88003 _88004 P h0 h1). Qed.
Lemma lem3387023 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term40 _88003 _88004 P.
Proof. exact (fun h0 : term38 _88003 _88004 P => @lem3387022 _88003 _88004 P h0). Qed.
Lemma lem3387026 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term38 _88003 _88004 P.
Proof. exact (@lem3387023 _88003 _88004 P (@lem3387015 _88003 _88004 P)). Qed.
Lemma lem3387027 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term38 _88003 _88004 P.
Proof. exact (@lem3387026 _88003 _88004 P). Qed.
Lemma lem3387033 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3387034 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term36 _88003 _88004 P) = (term41 _88003 _88004 P).
Proof. exact (@lem3387033 (term37 _88003 _88004 P)). Qed.
Lemma lem3387036 (t : Prop) : (term42 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3387037 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term41 _88003 _88004 P) = (term34 _88003 _88004 P).
Proof. exact (@lem3387036 (term34 _88003 _88004 P)). Qed.
Lemma lem3387042 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term36 _88003 _88004 P) = (term34 _88003 _88004 P).
Proof. exact (TRANS (@lem3387034 _88003 _88004 P) (@lem3387037 _88003 _88004 P)). Qed.
Lemma lem3387181 {_88003 _88004 : Type'} : (term43 _88003 _88004) = (term44 _88003 _88004).
Proof. exact (fun_ext (fun P : _88003 -> Prop => @lem3387042 _88003 _88004 P)). Qed.
Lemma lem3387182 {_88003 : Type'} : (@all (_88003 -> Prop)) = (@all (_88003 -> Prop)).
Proof. exact (eq_refl (@all (_88003 -> Prop))). Qed.
Lemma lem3387191 {_88003 _88004 : Type'} : (term45 _88003 _88004) = (term46 _88003 _88004).
Proof. exact (MK_COMB (@lem3387182 _88003) (@lem3387181 _88003 _88004)). Qed.
Lemma lem3387196 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term47 _88003 _88004 s P f x) = (term47 _88003 _88004 s P f x).
Proof. exact (eq_refl (term47 _88003 _88004 s P f x)). Qed.
Lemma lem3387197 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term48 _88003 _88004 s P f) = (term48 _88003 _88004 s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387196 _88003 _88004 s P f x)). Qed.
Lemma lem3387198 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387199 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term26 _88003 _88004 s P f) = (term26 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387198 _88004) (@lem3387197 _88003 _88004 s P f)). Qed.
Lemma lem3387200 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3387205 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term49 _88003 _88004 y f x s) = (term49 _88003 _88004 y f x s).
Proof. exact (eq_refl (term49 _88003 _88004 y f x s)). Qed.
Lemma lem3387206 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term50 _88003 _88004 y f s) = (term50 _88003 _88004 y f s).
Proof. exact (fun_ext (fun x : _88004 => @lem3387205 _88003 _88004 y f x s)). Qed.
Lemma lem3387207 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387208 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term15 _88003 _88004 y f s) = (term15 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387207 _88004) (@lem3387206 _88003 _88004 y f s)). Qed.
Lemma lem3387209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387210 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term17 _88003 _88004 y f s) = (term17 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387209) (@lem3387208 _88003 _88004 y f s)). Qed.
Lemma lem3387211 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term19 _88003 _88004 f s P y) = (term19 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387210 _88003 _88004 y f s) (@lem3387200 _88003 P y)). Qed.
Lemma lem3387212 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term21 _88003 _88004 f s P) = (term21 _88003 _88004 f s P).
Proof. exact (fun_ext (fun y : _88003 => @lem3387211 _88003 _88004 f s P y)). Qed.
Lemma lem3387213 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3387214 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term23 _88003 _88004 f s P) = (term23 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387213 _88003) (@lem3387212 _88003 _88004 f s P)). Qed.
Lemma lem3387215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3387216 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term25 _88003 _88004 f s P) = (term25 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387215) (@lem3387214 _88003 _88004 f s P)). Qed.
Lemma lem3387217 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : ((term23 _88003 _88004 f s P) = (term26 _88003 _88004 s P f)) = ((term23 _88003 _88004 f s P) = (term26 _88003 _88004 s P f)).
Proof. exact (MK_COMB (@lem3387216 _88003 _88004 f s P) (@lem3387199 _88003 _88004 s P f)). Qed.
Lemma lem3387218 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) : (term28 _88003 _88004 P f) = (term28 _88003 _88004 P f).
Proof. exact (fun_ext (fun s : _88004 -> Prop => @lem3387217 _88003 _88004 s P f)). Qed.
Lemma lem3387219 {_88004 : Type'} : (@all (_88004 -> Prop)) = (@all (_88004 -> Prop)).
Proof. exact (eq_refl (@all (_88004 -> Prop))). Qed.
Lemma lem3387220 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) : (term30 _88003 _88004 P f) = (term30 _88003 _88004 P f).
Proof. exact (MK_COMB (@lem3387219 _88004) (@lem3387218 _88003 _88004 P f)). Qed.
Lemma lem3387221 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term32 _88003 _88004 P) = (term32 _88003 _88004 P).
Proof. exact (fun_ext (fun f : _88004 -> _88003 => @lem3387220 _88003 _88004 P f)). Qed.
Lemma lem3387222 {_88003 _88004 : Type'} : (@all (_88004 -> _88003)) = (@all (_88004 -> _88003)).
Proof. exact (eq_refl (@all (_88004 -> _88003))). Qed.
Lemma lem3387223 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term34 _88003 _88004 P) = (term34 _88003 _88004 P).
Proof. exact (MK_COMB (@lem3387222 _88003 _88004) (@lem3387221 _88003 _88004 P)). Qed.
Lemma lem3387224 {_88003 _88004 : Type'} : (term44 _88003 _88004) = (term44 _88003 _88004).
Proof. exact (fun_ext (fun P : _88003 -> Prop => @lem3387223 _88003 _88004 P)). Qed.
Lemma lem3387225 {_88003 : Type'} : (@all (_88003 -> Prop)) = (@all (_88003 -> Prop)).
Proof. exact (eq_refl (@all (_88003 -> Prop))). Qed.
Lemma lem3387226 {_88003 _88004 : Type'} : (term46 _88003 _88004) = (term46 _88003 _88004).
Proof. exact (MK_COMB (@lem3387225 _88003) (@lem3387224 _88003 _88004)). Qed.
Lemma lem3387271 {_88003 _88004 : Type'} : (term45 _88003 _88004) = (term46 _88003 _88004).
Proof. exact (TRANS (@lem3387191 _88003 _88004) (@lem3387226 _88003 _88004)). Qed.
Lemma lem3387272 {_88003 _88004 : Type'} : (term46 _88003 _88004) = (term45 _88003 _88004).
Proof. exact (SYM (@lem3387271 _88003 _88004)). Qed.
Lemma lem3387274 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3387275 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : ((term23 _88003 _88004 f s P) = (term26 _88003 _88004 s P f)) = (term51 _88003 _88004 s P f).
Proof. exact (@lem3387274 ((term23 _88003 _88004 f s P) = (term26 _88003 _88004 s P f))). Qed.
Lemma lem3387276 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term51 _88003 _88004 s P f) = ((term23 _88003 _88004 f s P) = (term26 _88003 _88004 s P f)).
Proof. exact (SYM (@lem3387275 _88003 _88004 s P f)). Qed.
Lemma lem3387277 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term52 _88003 _88004 s P f) : term52 _88003 _88004 s P f.
Proof. exact (h1). Qed.
Lemma lem3387286 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term53 _88003 _88004 y f x s) = (term54 _88003 _88004 y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN _88004 x s)). Qed.
Lemma lem3387289 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term49 _88003 _88004 y f x s) = (term49 _88003 _88004 y f x s).
Proof. exact (eq_refl (term49 _88003 _88004 y f x s)). Qed.
Lemma lem3387290 {_88004 : Type'} (P : _88004 -> Prop) : (term55 _88004 P) = (term56 _88004 P).
Proof. exact (@lem18394 _88004 P). Qed.
Lemma lem3387291 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term57 _88003 _88004 y f s) = (term58 _88003 _88004 y f s).
Proof. exact (@lem3387290 _88004 (term50 _88003 _88004 y f s)). Qed.
Lemma lem3387292 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term59 _88003 _88004 y f s x) = (term49 _88003 _88004 y f x s).
Proof. exact (eq_refl (term59 _88003 _88004 y f s x)). Qed.
Lemma lem3387293 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3387294 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term60 _88003 _88004 y f s x) = (term53 _88003 _88004 y f x s).
Proof. exact (MK_COMB (@lem3387293) (@lem3387292 _88003 _88004 y f x s)). Qed.
Lemma lem3387295 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term60 _88003 _88004 y f s x) = (term54 _88003 _88004 y f x s).
Proof. exact (TRANS (@lem3387294 _88003 _88004 y f x s) (@lem3387286 _88003 _88004 y f x s)). Qed.
Lemma lem3387296 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term61 _88003 _88004 y f s) = (term62 _88003 _88004 y f s).
Proof. exact (fun_ext (fun x : _88004 => @lem3387295 _88003 _88004 y f x s)). Qed.
Lemma lem3387297 {_88004 : Type'} : (@all _88004) = (@all _88004).
Proof. exact (eq_refl (@all _88004)). Qed.
Lemma lem3387298 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term58 _88003 _88004 y f s) = (term63 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387297 _88004) (@lem3387296 _88003 _88004 y f s)). Qed.
Lemma lem3387299 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term57 _88003 _88004 y f s) = (term63 _88003 _88004 y f s).
Proof. exact (TRANS (@lem3387291 _88003 _88004 y f s) (@lem3387298 _88003 _88004 y f s)). Qed.
Lemma lem3387300 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term50 _88003 _88004 y f s) = (term50 _88003 _88004 y f s).
Proof. exact (fun_ext (fun x : _88004 => @lem3387289 _88003 _88004 y f x s)). Qed.
Lemma lem3387301 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387302 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term15 _88003 _88004 y f s) = (term15 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387301 _88004) (@lem3387300 _88003 _88004 y f s)). Qed.
Lemma lem3387303 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (term64 _88003 P y) = (term64 _88003 P y).
Proof. exact (eq_refl (term64 _88003 P y)). Qed.
Lemma lem3387304 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3387305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387306 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term65 _88003 _88004 y f s) = (term66 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387305) (@lem3387299 _88003 _88004 y f s)). Qed.
Lemma lem3387307 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term67 _88003 _88004 f s P y) = (term68 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387306 _88003 _88004 y f s) (@lem3387303 _88003 P y)). Qed.
Lemma lem3387308 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term69 _88003 _88004 f s P y) = (term67 _88003 _88004 f s P y).
Proof. exact (@lem17045 (term15 _88003 _88004 y f s) (P y)). Qed.
Lemma lem3387309 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term69 _88003 _88004 f s P y) = (term68 _88003 _88004 f s P y).
Proof. exact (TRANS (@lem3387308 _88003 _88004 f s P y) (@lem3387307 _88003 _88004 f s P y)). Qed.
Lemma lem3387310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387311 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term17 _88003 _88004 y f s) = (term17 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387310) (@lem3387302 _88003 _88004 y f s)). Qed.
Lemma lem3387312 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term19 _88003 _88004 f s P y) = (term19 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387311 _88003 _88004 y f s) (@lem3387304 _88003 P y)). Qed.
Lemma lem3387313 {_88003 : Type'} (P : _88003 -> Prop) : (term55 _88003 P) = (term56 _88003 P).
Proof. exact (@lem18394 _88003 P). Qed.
Lemma lem3387314 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term70 _88003 _88004 f s P) = (term71 _88003 _88004 f s P).
Proof. exact (@lem3387313 _88003 (term21 _88003 _88004 f s P)). Qed.
Lemma lem3387315 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term72 _88003 _88004 f s P y) = (term19 _88003 _88004 f s P y).
Proof. exact (eq_refl (term72 _88003 _88004 f s P y)). Qed.
Lemma lem3387316 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3387317 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term73 _88003 _88004 f s P y) = (term69 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387316) (@lem3387315 _88003 _88004 f s P y)). Qed.
Lemma lem3387318 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term73 _88003 _88004 f s P y) = (term68 _88003 _88004 f s P y).
Proof. exact (TRANS (@lem3387317 _88003 _88004 f s P y) (@lem3387309 _88003 _88004 f s P y)). Qed.
Lemma lem3387319 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term74 _88003 _88004 f s P) = (term75 _88003 _88004 f s P).
Proof. exact (fun_ext (fun y : _88003 => @lem3387318 _88003 _88004 f s P y)). Qed.
Lemma lem3387320 {_88003 : Type'} : (@all _88003) = (@all _88003).
Proof. exact (eq_refl (@all _88003)). Qed.
Lemma lem3387321 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term71 _88003 _88004 f s P) = (term76 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387320 _88003) (@lem3387319 _88003 _88004 f s P)). Qed.
Lemma lem3387322 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term70 _88003 _88004 f s P) = (term76 _88003 _88004 f s P).
Proof. exact (TRANS (@lem3387314 _88003 _88004 f s P) (@lem3387321 _88003 _88004 f s P)). Qed.
Lemma lem3387323 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term21 _88003 _88004 f s P) = (term21 _88003 _88004 f s P).
Proof. exact (fun_ext (fun y : _88003 => @lem3387312 _88003 _88004 f s P y)). Qed.
Lemma lem3387324 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3387325 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term23 _88003 _88004 f s P) = (term23 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387324 _88003) (@lem3387323 _88003 _88004 f s P)). Qed.
Lemma lem3387334 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term77 _88003 _88004 s P f x) = (term78 _88003 _88004 s P f x).
Proof. exact (@lem17045 (@IN _88004 x s) (term79 _88003 _88004 P f x)). Qed.
Lemma lem3387337 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term47 _88003 _88004 s P f x) = (term47 _88003 _88004 s P f x).
Proof. exact (eq_refl (term47 _88003 _88004 s P f x)). Qed.
Lemma lem3387338 {_88004 : Type'} (P : _88004 -> Prop) : (term55 _88004 P) = (term56 _88004 P).
Proof. exact (@lem18394 _88004 P). Qed.
Lemma lem3387339 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term80 _88003 _88004 s P f) = (term81 _88003 _88004 s P f).
Proof. exact (@lem3387338 _88004 (term48 _88003 _88004 s P f)). Qed.
Lemma lem3387340 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term82 _88003 _88004 s P f x) = (term47 _88003 _88004 s P f x).
Proof. exact (eq_refl (term82 _88003 _88004 s P f x)). Qed.
Lemma lem3387341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3387342 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term83 _88003 _88004 s P f x) = (term77 _88003 _88004 s P f x).
Proof. exact (MK_COMB (@lem3387341) (@lem3387340 _88003 _88004 s P f x)). Qed.
Lemma lem3387343 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term83 _88003 _88004 s P f x) = (term78 _88003 _88004 s P f x).
Proof. exact (TRANS (@lem3387342 _88003 _88004 s P f x) (@lem3387334 _88003 _88004 s P f x)). Qed.
Lemma lem3387344 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term84 _88003 _88004 s P f) = (term85 _88003 _88004 s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387343 _88003 _88004 s P f x)). Qed.
Lemma lem3387345 {_88004 : Type'} : (@all _88004) = (@all _88004).
Proof. exact (eq_refl (@all _88004)). Qed.
Lemma lem3387346 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term81 _88003 _88004 s P f) = (term86 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387345 _88004) (@lem3387344 _88003 _88004 s P f)). Qed.
Lemma lem3387347 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term80 _88003 _88004 s P f) = (term86 _88003 _88004 s P f).
Proof. exact (TRANS (@lem3387339 _88003 _88004 s P f) (@lem3387346 _88003 _88004 s P f)). Qed.
Lemma lem3387348 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term48 _88003 _88004 s P f) = (term48 _88003 _88004 s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387337 _88003 _88004 s P f x)). Qed.
Lemma lem3387349 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387350 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term26 _88003 _88004 s P f) = (term26 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387349 _88004) (@lem3387348 _88003 _88004 s P f)). Qed.
Lemma lem3387351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387352 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term87 _88003 _88004 f s P) = (term88 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387351) (@lem3387322 _88003 _88004 f s P)). Qed.
Lemma lem3387353 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term89 _88003 _88004 s P f) = (term90 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387352 _88003 _88004 f s P) (@lem3387350 _88003 _88004 s P f)). Qed.
Lemma lem3387354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387355 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term91 _88003 _88004 f s P) = (term91 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387354) (@lem3387325 _88003 _88004 f s P)). Qed.
Lemma lem3387356 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term92 _88003 _88004 s P f) = (term93 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387355 _88003 _88004 f s P) (@lem3387347 _88003 _88004 s P f)). Qed.
Lemma lem3387357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387358 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term94 _88003 _88004 s P f) = (term95 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387357) (@lem3387356 _88003 _88004 s P f)). Qed.
Lemma lem3387359 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term96 _88003 _88004 s P f) = (term97 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387358 _88003 _88004 s P f) (@lem3387353 _88003 _88004 s P f)). Qed.
Lemma lem3387360 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term52 _88003 _88004 s P f) = (term96 _88003 _88004 s P f).
Proof. exact (@lem17646 (term23 _88003 _88004 f s P) (term26 _88003 _88004 s P f)). Qed.
Lemma lem3387361 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term52 _88003 _88004 s P f) = (term97 _88003 _88004 s P f).
Proof. exact (TRANS (@lem3387360 _88003 _88004 s P f) (@lem3387359 _88003 _88004 s P f)). Qed.
Lemma lem3387636 {A : Type'} (P : A -> Prop) (Q : Prop) : (term98 A P Q) = (term99 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3387637 {_88004 : Type'} (P : _88004 -> Prop) (Q : Prop) : (term98 _88004 P Q) = (term99 _88004 P Q).
Proof. exact (@lem3387636 _88004 P Q). Qed.
Lemma lem3387638 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term100 _88003 _88004 f s P y) = (term101 _88003 _88004 f s P y).
Proof. exact (@lem3387637 _88004 (term50 _88003 _88004 y f s) (P y)). Qed.
Lemma lem3387639 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term59 _88003 _88004 y f s x) = (term49 _88003 _88004 y f x s).
Proof. exact (eq_refl (term59 _88003 _88004 y f s x)). Qed.
Lemma lem3387640 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term102 _88003 _88004 y f s) = (term50 _88003 _88004 y f s).
Proof. exact (fun_ext (fun x : _88004 => @lem3387639 _88003 _88004 y f x s)). Qed.
Lemma lem3387641 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387642 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term103 _88003 _88004 y f s) = (term15 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387641 _88004) (@lem3387640 _88003 _88004 y f s)). Qed.
Lemma lem3387643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387644 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term104 _88003 _88004 y f s) = (term17 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387643) (@lem3387642 _88003 _88004 y f s)). Qed.
Lemma lem3387645 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3387646 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term100 _88003 _88004 f s P y) = (term19 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387644 _88003 _88004 y f s) (@lem3387645 _88003 P y)). Qed.
Lemma lem3387647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3387648 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term105 _88003 _88004 f s P y) = (term106 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387647) (@lem3387646 _88003 _88004 f s P y)). Qed.
Lemma lem3387649 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term59 _88003 _88004 y f s x) = (term49 _88003 _88004 y f x s).
Proof. exact (eq_refl (term59 _88003 _88004 y f s x)). Qed.
Lemma lem3387650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387651 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term107 _88003 _88004 y f s x) = (term108 _88003 _88004 y f x s).
Proof. exact (MK_COMB (@lem3387650) (@lem3387649 _88003 _88004 y f x s)). Qed.
Lemma lem3387652 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3387653 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term109 _88003 _88004 f s x P y) = (term110 _88003 _88004 f x s P y).
Proof. exact (MK_COMB (@lem3387651 _88003 _88004 y f x s) (@lem3387652 _88003 P y)). Qed.
Lemma lem3387654 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term111 _88003 _88004 f s P y) = (term112 _88003 _88004 f s P y).
Proof. exact (fun_ext (fun x : _88004 => @lem3387653 _88003 _88004 f x s P y)). Qed.
Lemma lem3387655 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387656 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term101 _88003 _88004 f s P y) = (term113 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387655 _88004) (@lem3387654 _88003 _88004 f s P y)). Qed.
Lemma lem3387657 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : ((term100 _88003 _88004 f s P y) = (term101 _88003 _88004 f s P y)) = ((term19 _88003 _88004 f s P y) = (term113 _88003 _88004 f s P y)).
Proof. exact (MK_COMB (@lem3387648 _88003 _88004 f s P y) (@lem3387656 _88003 _88004 f s P y)). Qed.
Lemma lem3387658 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term19 _88003 _88004 f s P y) = (term113 _88003 _88004 f s P y).
Proof. exact (EQ_MP (@lem3387657 _88003 _88004 f s P y) (@lem3387638 _88003 _88004 f s P y)). Qed.
Lemma lem3387659 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term21 _88003 _88004 f s P) = (term114 _88003 _88004 f s P).
Proof. exact (fun_ext (fun y : _88003 => @lem3387658 _88003 _88004 f s P y)). Qed.
Lemma lem3387660 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3387661 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term23 _88003 _88004 f s P) = (term115 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387660 _88003) (@lem3387659 _88003 _88004 f s P)). Qed.
Lemma lem3387662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387663 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term91 _88003 _88004 f s P) = (term116 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387662) (@lem3387661 _88003 _88004 f s P)). Qed.
Lemma lem3387664 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term86 _88003 _88004 s P f) = (term86 _88003 _88004 s P f).
Proof. exact (eq_refl (term86 _88003 _88004 s P f)). Qed.
Lemma lem3387665 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term93 _88003 _88004 s P f) = (term117 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387663 _88003 _88004 f s P) (@lem3387664 _88003 _88004 s P f)). Qed.
Lemma lem3387667 {A : Type'} (P : A -> Prop) (Q : Prop) : (term98 A P Q) = (term99 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3387668 {_88003 : Type'} (P : _88003 -> Prop) (Q : Prop) : (term98 _88003 P Q) = (term99 _88003 P Q).
Proof. exact (@lem3387667 _88003 P Q). Qed.
Lemma lem3387669 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term118 _88003 _88004 s P f) = (term119 _88003 _88004 s P f).
Proof. exact (@lem3387668 _88003 (term114 _88003 _88004 f s P) (term86 _88003 _88004 s P f)). Qed.
Lemma lem3387670 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term120 _88003 _88004 f s P y) = (term113 _88003 _88004 f s P y).
Proof. exact (eq_refl (term120 _88003 _88004 f s P y)). Qed.
Lemma lem3387671 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term121 _88003 _88004 f s P) = (term114 _88003 _88004 f s P).
Proof. exact (fun_ext (fun y : _88003 => @lem3387670 _88003 _88004 f s P y)). Qed.
Lemma lem3387672 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3387673 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term122 _88003 _88004 f s P) = (term115 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387672 _88003) (@lem3387671 _88003 _88004 f s P)). Qed.
Lemma lem3387674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387675 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term123 _88003 _88004 f s P) = (term116 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387674) (@lem3387673 _88003 _88004 f s P)). Qed.
Lemma lem3387676 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term86 _88003 _88004 s P f) = (term86 _88003 _88004 s P f).
Proof. exact (eq_refl (term86 _88003 _88004 s P f)). Qed.
Lemma lem3387677 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term118 _88003 _88004 s P f) = (term117 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387675 _88003 _88004 f s P) (@lem3387676 _88003 _88004 s P f)). Qed.
Lemma lem3387678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3387679 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term124 _88003 _88004 s P f) = (term125 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387678) (@lem3387677 _88003 _88004 s P f)). Qed.
Lemma lem3387680 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term120 _88003 _88004 f s P y) = (term113 _88003 _88004 f s P y).
Proof. exact (eq_refl (term120 _88003 _88004 f s P y)). Qed.
Lemma lem3387681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387682 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term126 _88003 _88004 f s P y) = (term127 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387681) (@lem3387680 _88003 _88004 f s P y)). Qed.
Lemma lem3387683 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term86 _88003 _88004 s P f) = (term86 _88003 _88004 s P f).
Proof. exact (eq_refl (term86 _88003 _88004 s P f)). Qed.
Lemma lem3387684 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term128 _88003 _88004 y s P f) = (term129 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387682 _88003 _88004 f s P y) (@lem3387683 _88003 _88004 s P f)). Qed.
Lemma lem3387685 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term130 _88003 _88004 s P f) = (term131 _88003 _88004 s P f).
Proof. exact (fun_ext (fun y : _88003 => @lem3387684 _88003 _88004 y s P f)). Qed.
Lemma lem3387686 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3387687 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term119 _88003 _88004 s P f) = (term132 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387686 _88003) (@lem3387685 _88003 _88004 s P f)). Qed.
Lemma lem3387688 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : ((term118 _88003 _88004 s P f) = (term119 _88003 _88004 s P f)) = ((term117 _88003 _88004 s P f) = (term132 _88003 _88004 s P f)).
Proof. exact (MK_COMB (@lem3387679 _88003 _88004 s P f) (@lem3387687 _88003 _88004 s P f)). Qed.
Lemma lem3387689 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term117 _88003 _88004 s P f) = (term132 _88003 _88004 s P f).
Proof. exact (EQ_MP (@lem3387688 _88003 _88004 s P f) (@lem3387669 _88003 _88004 s P f)). Qed.
Lemma lem3387691 {A : Type'} (P : A -> Prop) (Q : Prop) : (term98 A P Q) = (term99 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3387692 {_88004 : Type'} (P : _88004 -> Prop) (Q : Prop) : (term98 _88004 P Q) = (term99 _88004 P Q).
Proof. exact (@lem3387691 _88004 P Q). Qed.
Lemma lem3387693 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term133 _88003 _88004 y s P f) = (term134 _88003 _88004 y s P f).
Proof. exact (@lem3387692 _88004 (term112 _88003 _88004 f s P y) (term86 _88003 _88004 s P f)). Qed.
Lemma lem3387694 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term135 _88003 _88004 f s P y x) = (term110 _88003 _88004 f x s P y).
Proof. exact (eq_refl (term135 _88003 _88004 f s P y x)). Qed.
Lemma lem3387695 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term136 _88003 _88004 f s P y) = (term112 _88003 _88004 f s P y).
Proof. exact (fun_ext (fun x : _88004 => @lem3387694 _88003 _88004 f x s P y)). Qed.
Lemma lem3387696 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387697 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term137 _88003 _88004 f s P y) = (term113 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387696 _88004) (@lem3387695 _88003 _88004 f s P y)). Qed.
Lemma lem3387698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387699 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term138 _88003 _88004 f s P y) = (term127 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387698) (@lem3387697 _88003 _88004 f s P y)). Qed.
Lemma lem3387700 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term86 _88003 _88004 s P f) = (term86 _88003 _88004 s P f).
Proof. exact (eq_refl (term86 _88003 _88004 s P f)). Qed.
Lemma lem3387701 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term133 _88003 _88004 y s P f) = (term129 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387699 _88003 _88004 f s P y) (@lem3387700 _88003 _88004 s P f)). Qed.
Lemma lem3387702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3387703 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term139 _88003 _88004 y s P f) = (term140 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387702) (@lem3387701 _88003 _88004 y s P f)). Qed.
Lemma lem3387704 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term135 _88003 _88004 f s P y x) = (term110 _88003 _88004 f x s P y).
Proof. exact (eq_refl (term135 _88003 _88004 f s P y x)). Qed.
Lemma lem3387705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387706 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term141 _88003 _88004 f s P y x) = (term142 _88003 _88004 f x s P y).
Proof. exact (MK_COMB (@lem3387705) (@lem3387704 _88003 _88004 f x s P y)). Qed.
Lemma lem3387707 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term86 _88003 _88004 s P f) = (term86 _88003 _88004 s P f).
Proof. exact (eq_refl (term86 _88003 _88004 s P f)). Qed.
Lemma lem3387708 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term143 _88003 _88004 y x s P f) = (term144 _88003 _88004 x y s P f).
Proof. exact (MK_COMB (@lem3387706 _88003 _88004 f x s P y) (@lem3387707 _88003 _88004 s P f)). Qed.
Lemma lem3387709 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term145 _88003 _88004 y s P f) = (term146 _88003 _88004 y s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387708 _88003 _88004 x y s P f)). Qed.
Lemma lem3387710 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387711 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term134 _88003 _88004 y s P f) = (term147 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387710 _88004) (@lem3387709 _88003 _88004 y s P f)). Qed.
Lemma lem3387712 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : ((term133 _88003 _88004 y s P f) = (term134 _88003 _88004 y s P f)) = ((term129 _88003 _88004 y s P f) = (term147 _88003 _88004 y s P f)).
Proof. exact (MK_COMB (@lem3387703 _88003 _88004 y s P f) (@lem3387711 _88003 _88004 y s P f)). Qed.
Lemma lem3387713 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term129 _88003 _88004 y s P f) = (term147 _88003 _88004 y s P f).
Proof. exact (EQ_MP (@lem3387712 _88003 _88004 y s P f) (@lem3387693 _88003 _88004 y s P f)). Qed.
Lemma lem3387714 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term131 _88003 _88004 s P f) = (term148 _88003 _88004 s P f).
Proof. exact (fun_ext (fun y : _88003 => @lem3387713 _88003 _88004 y s P f)). Qed.
Lemma lem3387715 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3387716 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term132 _88003 _88004 s P f) = (term149 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387715 _88003) (@lem3387714 _88003 _88004 s P f)). Qed.
Lemma lem3387717 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term117 _88003 _88004 s P f) = (term149 _88003 _88004 s P f).
Proof. exact (TRANS (@lem3387689 _88003 _88004 s P f) (@lem3387716 _88003 _88004 s P f)). Qed.
Lemma lem3387718 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term93 _88003 _88004 s P f) = (term149 _88003 _88004 s P f).
Proof. exact (TRANS (@lem3387665 _88003 _88004 s P f) (@lem3387717 _88003 _88004 s P f)). Qed.
Lemma lem3387719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387720 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term95 _88003 _88004 s P f) = (term150 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387719) (@lem3387718 _88003 _88004 s P f)). Qed.
Lemma lem3387722 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3387723 {_88004 : Type'} (P : Prop) (Q : _88004 -> Prop) : (term151 _88004 P Q) = (term152 _88004 P Q).
Proof. exact (@lem3387722 _88004 P Q). Qed.
Lemma lem3387724 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term153 _88003 _88004 s P f) = (term154 _88003 _88004 s P f).
Proof. exact (@lem3387723 _88004 (term76 _88003 _88004 f s P) (term48 _88003 _88004 s P f)). Qed.
Lemma lem3387725 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term82 _88003 _88004 s P f x) = (term47 _88003 _88004 s P f x).
Proof. exact (eq_refl (term82 _88003 _88004 s P f x)). Qed.
Lemma lem3387726 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term155 _88003 _88004 s P f) = (term48 _88003 _88004 s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387725 _88003 _88004 s P f x)). Qed.
Lemma lem3387727 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387728 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term156 _88003 _88004 s P f) = (term26 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387727 _88004) (@lem3387726 _88003 _88004 s P f)). Qed.
Lemma lem3387729 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term88 _88003 _88004 f s P) = (term88 _88003 _88004 f s P).
Proof. exact (eq_refl (term88 _88003 _88004 f s P)). Qed.
Lemma lem3387730 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term153 _88003 _88004 s P f) = (term90 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387729 _88003 _88004 f s P) (@lem3387728 _88003 _88004 s P f)). Qed.
Lemma lem3387731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3387732 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term157 _88003 _88004 s P f) = (term158 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387731) (@lem3387730 _88003 _88004 s P f)). Qed.
Lemma lem3387733 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term82 _88003 _88004 s P f x) = (term47 _88003 _88004 s P f x).
Proof. exact (eq_refl (term82 _88003 _88004 s P f x)). Qed.
Lemma lem3387734 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term88 _88003 _88004 f s P) = (term88 _88003 _88004 f s P).
Proof. exact (eq_refl (term88 _88003 _88004 f s P)). Qed.
Lemma lem3387735 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term159 _88003 _88004 s P f x) = (term160 _88003 _88004 s P f x).
Proof. exact (MK_COMB (@lem3387734 _88003 _88004 f s P) (@lem3387733 _88003 _88004 s P f x)). Qed.
Lemma lem3387736 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term161 _88003 _88004 s P f) = (term162 _88003 _88004 s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387735 _88003 _88004 s P f x)). Qed.
Lemma lem3387737 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387738 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term154 _88003 _88004 s P f) = (term163 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387737 _88004) (@lem3387736 _88003 _88004 s P f)). Qed.
Lemma lem3387739 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : ((term153 _88003 _88004 s P f) = (term154 _88003 _88004 s P f)) = ((term90 _88003 _88004 s P f) = (term163 _88003 _88004 s P f)).
Proof. exact (MK_COMB (@lem3387732 _88003 _88004 s P f) (@lem3387738 _88003 _88004 s P f)). Qed.
Lemma lem3387740 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term90 _88003 _88004 s P f) = (term163 _88003 _88004 s P f).
Proof. exact (EQ_MP (@lem3387739 _88003 _88004 s P f) (@lem3387724 _88003 _88004 s P f)). Qed.
Lemma lem3387741 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term97 _88003 _88004 s P f) = (term164 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387720 _88003 _88004 s P f) (@lem3387740 _88003 _88004 s P f)). Qed.
Lemma lem3387745 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3387746 {_88003 : Type'} (P : _88003 -> Prop) (Q : Prop) : (term165 _88003 P Q) = (term166 _88003 P Q).
Proof. exact (@lem3387745 _88003 P Q). Qed.
Lemma lem3387747 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term167 _88003 _88004 s P f) = (term168 _88003 _88004 s P f).
Proof. exact (@lem3387746 _88003 (term148 _88003 _88004 s P f) (term163 _88003 _88004 s P f)). Qed.
Lemma lem3387748 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term169 _88003 _88004 s P f y) = (term147 _88003 _88004 y s P f).
Proof. exact (eq_refl (term169 _88003 _88004 s P f y)). Qed.
Lemma lem3387749 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term170 _88003 _88004 s P f) = (term148 _88003 _88004 s P f).
Proof. exact (fun_ext (fun y : _88003 => @lem3387748 _88003 _88004 y s P f)). Qed.
Lemma lem3387750 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3387751 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term171 _88003 _88004 s P f) = (term149 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387750 _88003) (@lem3387749 _88003 _88004 s P f)). Qed.
Lemma lem3387752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387753 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term172 _88003 _88004 s P f) = (term150 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387752) (@lem3387751 _88003 _88004 s P f)). Qed.
Lemma lem3387754 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term163 _88003 _88004 s P f) = (term163 _88003 _88004 s P f).
Proof. exact (eq_refl (term163 _88003 _88004 s P f)). Qed.
Lemma lem3387755 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term167 _88003 _88004 s P f) = (term164 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387753 _88003 _88004 s P f) (@lem3387754 _88003 _88004 s P f)). Qed.
Lemma lem3387756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3387757 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term173 _88003 _88004 s P f) = (term174 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387756) (@lem3387755 _88003 _88004 s P f)). Qed.
Lemma lem3387758 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term169 _88003 _88004 s P f y) = (term147 _88003 _88004 y s P f).
Proof. exact (eq_refl (term169 _88003 _88004 s P f y)). Qed.
Lemma lem3387759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387760 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term175 _88003 _88004 s P f y) = (term176 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387759) (@lem3387758 _88003 _88004 y s P f)). Qed.
Lemma lem3387761 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term163 _88003 _88004 s P f) = (term163 _88003 _88004 s P f).
Proof. exact (eq_refl (term163 _88003 _88004 s P f)). Qed.
Lemma lem3387762 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term177 _88003 _88004 y s P f) = (term178 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387760 _88003 _88004 y s P f) (@lem3387761 _88003 _88004 s P f)). Qed.
Lemma lem3387763 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term179 _88003 _88004 s P f) = (term180 _88003 _88004 s P f).
Proof. exact (fun_ext (fun y : _88003 => @lem3387762 _88003 _88004 y s P f)). Qed.
Lemma lem3387764 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3387765 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term168 _88003 _88004 s P f) = (term181 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387764 _88003) (@lem3387763 _88003 _88004 s P f)). Qed.
Lemma lem3387766 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : ((term167 _88003 _88004 s P f) = (term168 _88003 _88004 s P f)) = ((term164 _88003 _88004 s P f) = (term181 _88003 _88004 s P f)).
Proof. exact (MK_COMB (@lem3387757 _88003 _88004 s P f) (@lem3387765 _88003 _88004 s P f)). Qed.
Lemma lem3387767 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term164 _88003 _88004 s P f) = (term181 _88003 _88004 s P f).
Proof. exact (EQ_MP (@lem3387766 _88003 _88004 s P f) (@lem3387747 _88003 _88004 s P f)). Qed.
Lemma lem3387769 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3387770 {_88004 : Type'} (P : _88004 -> Prop) (Q : _88004 -> Prop) : (term182 _88004 P Q) = (term183 _88004 P Q).
Proof. exact (@lem3387769 _88004 P Q). Qed.
Lemma lem3387771 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term184 _88003 _88004 y s P f) = (term185 _88003 _88004 y s P f).
Proof. exact (@lem3387770 _88004 (term146 _88003 _88004 y s P f) (term162 _88003 _88004 s P f)). Qed.
Lemma lem3387772 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term186 _88003 _88004 y s P f x) = (term144 _88003 _88004 x y s P f).
Proof. exact (eq_refl (term186 _88003 _88004 y s P f x)). Qed.
Lemma lem3387773 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term187 _88003 _88004 y s P f) = (term146 _88003 _88004 y s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387772 _88003 _88004 x y s P f)). Qed.
Lemma lem3387774 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387775 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term188 _88003 _88004 y s P f) = (term147 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387774 _88004) (@lem3387773 _88003 _88004 y s P f)). Qed.
Lemma lem3387776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387777 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term189 _88003 _88004 y s P f) = (term176 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387776) (@lem3387775 _88003 _88004 y s P f)). Qed.
Lemma lem3387778 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term190 _88003 _88004 s P f x) = (term160 _88003 _88004 s P f x).
Proof. exact (eq_refl (term190 _88003 _88004 s P f x)). Qed.
Lemma lem3387779 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term191 _88003 _88004 s P f) = (term162 _88003 _88004 s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387778 _88003 _88004 s P f x)). Qed.
Lemma lem3387780 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387781 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term192 _88003 _88004 s P f) = (term163 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387780 _88004) (@lem3387779 _88003 _88004 s P f)). Qed.
Lemma lem3387782 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term184 _88003 _88004 y s P f) = (term178 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387777 _88003 _88004 y s P f) (@lem3387781 _88003 _88004 s P f)). Qed.
Lemma lem3387783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3387784 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term193 _88003 _88004 y s P f) = (term194 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387783) (@lem3387782 _88003 _88004 y s P f)). Qed.
Lemma lem3387785 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term186 _88003 _88004 y s P f x) = (term144 _88003 _88004 x y s P f).
Proof. exact (eq_refl (term186 _88003 _88004 y s P f x)). Qed.
Lemma lem3387786 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387787 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term195 _88003 _88004 y s P f x) = (term196 _88003 _88004 x y s P f).
Proof. exact (MK_COMB (@lem3387786) (@lem3387785 _88003 _88004 x y s P f)). Qed.
Lemma lem3387788 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term190 _88003 _88004 s P f x) = (term160 _88003 _88004 s P f x).
Proof. exact (eq_refl (term190 _88003 _88004 s P f x)). Qed.
Lemma lem3387789 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term197 _88003 _88004 y s P f x) = (term198 _88003 _88004 y s P f x).
Proof. exact (MK_COMB (@lem3387787 _88003 _88004 x y s P f) (@lem3387788 _88003 _88004 s P f x)). Qed.
Lemma lem3387790 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term199 _88003 _88004 y s P f) = (term200 _88003 _88004 y s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387789 _88003 _88004 y s P f x)). Qed.
Lemma lem3387791 {_88004 : Type'} : (@ex _88004) = (@ex _88004).
Proof. exact (eq_refl (@ex _88004)). Qed.
Lemma lem3387792 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term185 _88003 _88004 y s P f) = (term201 _88003 _88004 y s P f).
Proof. exact (MK_COMB (@lem3387791 _88004) (@lem3387790 _88003 _88004 y s P f)). Qed.
Lemma lem3387793 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : ((term184 _88003 _88004 y s P f) = (term185 _88003 _88004 y s P f)) = ((term178 _88003 _88004 y s P f) = (term201 _88003 _88004 y s P f)).
Proof. exact (MK_COMB (@lem3387784 _88003 _88004 y s P f) (@lem3387792 _88003 _88004 y s P f)). Qed.
Lemma lem3387794 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term178 _88003 _88004 y s P f) = (term201 _88003 _88004 y s P f).
Proof. exact (EQ_MP (@lem3387793 _88003 _88004 y s P f) (@lem3387771 _88003 _88004 y s P f)). Qed.
Lemma lem3387795 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term180 _88003 _88004 s P f) = (term202 _88003 _88004 s P f).
Proof. exact (fun_ext (fun y : _88003 => @lem3387794 _88003 _88004 y s P f)). Qed.
Lemma lem3387796 {_88003 : Type'} : (@ex _88003) = (@ex _88003).
Proof. exact (eq_refl (@ex _88003)). Qed.
Lemma lem3387797 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term181 _88003 _88004 s P f) = (term203 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387796 _88003) (@lem3387795 _88003 _88004 s P f)). Qed.
Lemma lem3387798 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term164 _88003 _88004 s P f) = (term203 _88003 _88004 s P f).
Proof. exact (TRANS (@lem3387767 _88003 _88004 s P f) (@lem3387797 _88003 _88004 s P f)). Qed.
Lemma lem3387800 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term97 _88003 _88004 s P f) = (term203 _88003 _88004 s P f).
Proof. exact (TRANS (@lem3387741 _88003 _88004 s P f) (@lem3387798 _88003 _88004 s P f)). Qed.
Lemma lem3387801 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term52 _88003 _88004 s P f) = (term203 _88003 _88004 s P f).
Proof. exact (TRANS (@lem3387361 _88003 _88004 s P f) (@lem3387800 _88003 _88004 s P f)). Qed.
Lemma lem3387802 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term52 _88003 _88004 s P f) : term203 _88003 _88004 s P f.
Proof. exact (EQ_MP (@lem3387801 _88003 _88004 s P f) (@lem3387277 _88003 _88004 s P f h1)). Qed.
Lemma lem3387803 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term201 _88003 _88004 y s P f) : term201 _88003 _88004 y s P f.
Proof. exact (h1). Qed.
Lemma lem3387804 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term198 _88003 _88004 y s P f x) : term198 _88003 _88004 y s P f x.
Proof. exact (h1). Qed.
Lemma lem3387817 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term47 _88003 _88004 s P f x) = (term47 _88003 _88004 s P f x).
Proof. exact (eq_refl (term47 _88003 _88004 s P f x)). Qed.
Lemma lem3387822 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (term64 _88003 P y) = (term64 _88003 P y).
Proof. exact (eq_refl (term64 _88003 P y)). Qed.
Lemma lem3387841 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term54 _88003 _88004 y f x s) = (term54 _88003 _88004 y f x s).
Proof. exact (eq_refl (term54 _88003 _88004 y f x s)). Qed.
Lemma lem3387842 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term62 _88003 _88004 y f s) = (term62 _88003 _88004 y f s).
Proof. exact (fun_ext (fun x : _88004 => @lem3387841 _88003 _88004 y f x s)). Qed.
Lemma lem3387843 {_88004 : Type'} : (@all _88004) = (@all _88004).
Proof. exact (eq_refl (@all _88004)). Qed.
Lemma lem3387844 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term63 _88003 _88004 y f s) = (term63 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387843 _88004) (@lem3387842 _88003 _88004 y f s)). Qed.
Lemma lem3387845 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387846 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term66 _88003 _88004 y f s) = (term66 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387845) (@lem3387844 _88003 _88004 y f s)). Qed.
Lemma lem3387847 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term68 _88003 _88004 f s P y) = (term68 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387846 _88003 _88004 y f s) (@lem3387822 _88003 P y)). Qed.
Lemma lem3387848 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term75 _88003 _88004 f s P) = (term75 _88003 _88004 f s P).
Proof. exact (fun_ext (fun y : _88003 => @lem3387847 _88003 _88004 f s P y)). Qed.
Lemma lem3387849 {_88003 : Type'} : (@all _88003) = (@all _88003).
Proof. exact (eq_refl (@all _88003)). Qed.
Lemma lem3387850 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term76 _88003 _88004 f s P) = (term76 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387849 _88003) (@lem3387848 _88003 _88004 f s P)). Qed.
Lemma lem3387851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3387852 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term88 _88003 _88004 f s P) = (term88 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387851) (@lem3387850 _88003 _88004 f s P)). Qed.
Lemma lem3387853 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term160 _88003 _88004 s P f x) = (term160 _88003 _88004 s P f x).
Proof. exact (MK_COMB (@lem3387852 _88003 _88004 f s P) (@lem3387817 _88003 _88004 s P f x)). Qed.
Lemma lem3387870 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term78 _88003 _88004 s P f x) = (term78 _88003 _88004 s P f x).
Proof. exact (eq_refl (term78 _88003 _88004 s P f x)). Qed.
Lemma lem3387871 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term85 _88003 _88004 s P f) = (term85 _88003 _88004 s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387870 _88003 _88004 s P f x)). Qed.
Lemma lem3387872 {_88004 : Type'} : (@all _88004) = (@all _88004).
Proof. exact (eq_refl (@all _88004)). Qed.
Lemma lem3387873 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term86 _88003 _88004 s P f) = (term86 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387872 _88004) (@lem3387871 _88003 _88004 s P f)). Qed.
Lemma lem3387896 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term142 _88003 _88004 f x s P y) = (term142 _88003 _88004 f x s P y).
Proof. exact (eq_refl (term142 _88003 _88004 f x s P y)). Qed.
Lemma lem3387897 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term144 _88003 _88004 x y s P f) = (term144 _88003 _88004 x y s P f).
Proof. exact (MK_COMB (@lem3387896 _88003 _88004 f x s P y) (@lem3387873 _88003 _88004 s P f)). Qed.
Lemma lem3387898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387899 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term196 _88003 _88004 x y s P f) = (term196 _88003 _88004 x y s P f).
Proof. exact (MK_COMB (@lem3387898) (@lem3387897 _88003 _88004 x y s P f)). Qed.
Lemma lem3387900 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term198 _88003 _88004 y s P f x) = (term198 _88003 _88004 y s P f x).
Proof. exact (MK_COMB (@lem3387899 _88003 _88004 x y s P f) (@lem3387853 _88003 _88004 s P f x)). Qed.
Lemma lem3387901 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term198 _88003 _88004 y s P f x) : term198 _88003 _88004 y s P f x.
Proof. exact (EQ_MP (@lem3387900 _88003 _88004 y s P f x) (@lem3387804 _88003 _88004 y s P f x h1)). Qed.
Lemma lem3387902 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term144 _88003 _88004 x y s P f.
Proof. exact (h1). Qed.
Lemma lem3387903 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term160 _88003 _88004 s P f x.
Proof. exact (h1). Qed.
Lemma lem3387904 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term86 _88003 _88004 s P f.
Proof. exact (proj2 (@lem3387902 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3387905 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term110 _88003 _88004 f x s P y.
Proof. exact (proj1 (@lem3387902 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3387907 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term49 _88003 _88004 y f x s.
Proof. exact (proj1 (@lem3387905 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3387910 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term47 _88003 _88004 s P f x.
Proof. exact (proj2 (@lem3387903 _88003 _88004 s P f x h1)). Qed.
Lemma lem3387911 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term76 _88003 _88004 f s P.
Proof. exact (proj1 (@lem3387903 _88003 _88004 s P f x h1)). Qed.
Lemma lem3387921 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term78 _88003 _88004 s P f x) = (term78 _88003 _88004 s P f x).
Proof. exact (eq_refl (term78 _88003 _88004 s P f x)). Qed.
Lemma lem3387922 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term85 _88003 _88004 s P f) = (term85 _88003 _88004 s P f).
Proof. exact (fun_ext (fun x : _88004 => @lem3387921 _88003 _88004 s P f x)). Qed.
Lemma lem3387923 {_88004 : Type'} : (@all _88004) = (@all _88004).
Proof. exact (eq_refl (@all _88004)). Qed.
Lemma lem3387925 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term86 _88003 _88004 s P f) = (term86 _88003 _88004 s P f).
Proof. exact (MK_COMB (@lem3387923 _88004) (@lem3387922 _88003 _88004 s P f)). Qed.
Lemma lem3387926 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term86 _88003 _88004 s P f.
Proof. exact (EQ_MP (@lem3387925 _88003 _88004 s P f) (@lem3387904 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3387940 {A : Type'} (P : A -> Prop) (Q : Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3387941 {_88004 : Type'} (P : _88004 -> Prop) (Q : Prop) : (term204 _88004 P Q) = (term205 _88004 P Q).
Proof. exact (@lem3387940 _88004 P Q). Qed.
Lemma lem3387942 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term206 _88003 _88004 f s P y) = (term207 _88003 _88004 f s P y).
Proof. exact (@lem3387941 _88004 (term62 _88003 _88004 y f s) (term64 _88003 P y)). Qed.
Lemma lem3387943 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term208 _88003 _88004 y f s x) = (term54 _88003 _88004 y f x s).
Proof. exact (eq_refl (term208 _88003 _88004 y f s x)). Qed.
Lemma lem3387944 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term209 _88003 _88004 y f s) = (term62 _88003 _88004 y f s).
Proof. exact (fun_ext (fun x : _88004 => @lem3387943 _88003 _88004 y f x s)). Qed.
Lemma lem3387945 {_88004 : Type'} : (@all _88004) = (@all _88004).
Proof. exact (eq_refl (@all _88004)). Qed.
Lemma lem3387946 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term210 _88003 _88004 y f s) = (term63 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387945 _88004) (@lem3387944 _88003 _88004 y f s)). Qed.
Lemma lem3387947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387948 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (s : _88004 -> Prop) : (term211 _88003 _88004 y f s) = (term66 _88003 _88004 y f s).
Proof. exact (MK_COMB (@lem3387947) (@lem3387946 _88003 _88004 y f s)). Qed.
Lemma lem3387949 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (term64 _88003 P y) = (term64 _88003 P y).
Proof. exact (eq_refl (term64 _88003 P y)). Qed.
Lemma lem3387950 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term206 _88003 _88004 f s P y) = (term68 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387948 _88003 _88004 y f s) (@lem3387949 _88003 P y)). Qed.
Lemma lem3387951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3387952 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term212 _88003 _88004 f s P y) = (term213 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387951) (@lem3387950 _88003 _88004 f s P y)). Qed.
Lemma lem3387953 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term208 _88003 _88004 y f s x) = (term54 _88003 _88004 y f x s).
Proof. exact (eq_refl (term208 _88003 _88004 y f s x)). Qed.
Lemma lem3387954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3387955 {_88003 _88004 : Type'} (y : _88003) (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) : (term214 _88003 _88004 y f s x) = (term215 _88003 _88004 y f x s).
Proof. exact (MK_COMB (@lem3387954) (@lem3387953 _88003 _88004 y f x s)). Qed.
Lemma lem3387956 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (term64 _88003 P y) = (term64 _88003 P y).
Proof. exact (eq_refl (term64 _88003 P y)). Qed.
Lemma lem3387957 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term216 _88003 _88004 f s x P y) = (term217 _88003 _88004 f x s P y).
Proof. exact (MK_COMB (@lem3387955 _88003 _88004 y f x s) (@lem3387956 _88003 P y)). Qed.
Lemma lem3387958 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term218 _88003 _88004 f s P y) = (term219 _88003 _88004 f s P y).
Proof. exact (fun_ext (fun x : _88004 => @lem3387957 _88003 _88004 f x s P y)). Qed.
Lemma lem3387959 {_88004 : Type'} : (@all _88004) = (@all _88004).
Proof. exact (eq_refl (@all _88004)). Qed.
Lemma lem3387960 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term207 _88003 _88004 f s P y) = (term220 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387959 _88004) (@lem3387958 _88003 _88004 f s P y)). Qed.
Lemma lem3387961 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : ((term206 _88003 _88004 f s P y) = (term207 _88003 _88004 f s P y)) = ((term68 _88003 _88004 f s P y) = (term220 _88003 _88004 f s P y)).
Proof. exact (MK_COMB (@lem3387952 _88003 _88004 f s P y) (@lem3387960 _88003 _88004 f s P y)). Qed.
Lemma lem3387962 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term68 _88003 _88004 f s P y) = (term220 _88003 _88004 f s P y).
Proof. exact (EQ_MP (@lem3387961 _88003 _88004 f s P y) (@lem3387942 _88003 _88004 f s P y)). Qed.
Lemma lem3387963 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term75 _88003 _88004 f s P) = (term221 _88003 _88004 f s P).
Proof. exact (fun_ext (fun y : _88003 => @lem3387962 _88003 _88004 f s P y)). Qed.
Lemma lem3387964 {_88003 : Type'} : (@all _88003) = (@all _88003).
Proof. exact (eq_refl (@all _88003)). Qed.
Lemma lem3387965 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term76 _88003 _88004 f s P) = (term222 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387964 _88003) (@lem3387963 _88003 _88004 f s P)). Qed.
Lemma lem3387978 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term217 _88003 _88004 f x s P y) = (term217 _88003 _88004 f x s P y).
Proof. exact (eq_refl (term217 _88003 _88004 f x s P y)). Qed.
Lemma lem3387979 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term219 _88003 _88004 f s P y) = (term219 _88003 _88004 f s P y).
Proof. exact (fun_ext (fun x : _88004 => @lem3387978 _88003 _88004 f x s P y)). Qed.
Lemma lem3387980 {_88004 : Type'} : (@all _88004) = (@all _88004).
Proof. exact (eq_refl (@all _88004)). Qed.
Lemma lem3387981 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (y : _88003) : (term220 _88003 _88004 f s P y) = (term220 _88003 _88004 f s P y).
Proof. exact (MK_COMB (@lem3387980 _88004) (@lem3387979 _88003 _88004 f s P y)). Qed.
Lemma lem3387982 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term221 _88003 _88004 f s P) = (term221 _88003 _88004 f s P).
Proof. exact (fun_ext (fun y : _88003 => @lem3387981 _88003 _88004 f s P y)). Qed.
Lemma lem3387983 {_88003 : Type'} : (@all _88003) = (@all _88003).
Proof. exact (eq_refl (@all _88003)). Qed.
Lemma lem3387984 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term222 _88003 _88004 f s P) = (term222 _88003 _88004 f s P).
Proof. exact (MK_COMB (@lem3387983 _88003) (@lem3387982 _88003 _88004 f s P)). Qed.
Lemma lem3387985 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) : (term76 _88003 _88004 f s P) = (term222 _88003 _88004 f s P).
Proof. exact (TRANS (@lem3387965 _88003 _88004 f s P) (@lem3387984 _88003 _88004 f s P)). Qed.
Lemma lem3387986 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term222 _88003 _88004 f s P.
Proof. exact (EQ_MP (@lem3387985 _88003 _88004 f s P) (@lem3387911 _88003 _88004 s P f x h1)). Qed.
Lemma lem3387995 {_88003 _88004 : Type'} (_35583 : _88004) (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term223 _88003 _88004 s P f _35583.
Proof. exact (@lem3387926 _88003 _88004 x y s P f h1 _35583). Qed.
Lemma lem3387996 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (_35583 : _88004) : (term223 _88003 _88004 s P f _35583) = (term78 _88003 _88004 s P f _35583).
Proof. exact (eq_refl (term223 _88003 _88004 s P f _35583)). Qed.
Lemma lem3387998 {_88003 _88004 : Type'} (_35584 : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term224 _88003 _88004 f s P _35584.
Proof. exact (@lem3387986 _88003 _88004 s P f x h1 _35584). Qed.
Lemma lem3387999 {_88003 _88004 : Type'} (f : _88004 -> _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (_35584 : _88003) : (term224 _88003 _88004 f s P _35584) = (term220 _88003 _88004 f s P _35584).
Proof. exact (eq_refl (term224 _88003 _88004 f s P _35584)). Qed.
Lemma lem3388000 {_88003 _88004 : Type'} (_35584 : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term220 _88003 _88004 f s P _35584.
Proof. exact (EQ_MP (@lem3387999 _88003 _88004 f s P _35584) (@lem3387998 _88003 _88004 _35584 s P f x h1)). Qed.
Lemma lem3388001 {_88003 _88004 : Type'} (_35584 : _88003) (_35585 : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term225 _88003 _88004 f s P _35584 _35585.
Proof. exact (@lem3388000 _88003 _88004 _35584 s P f x h1 _35585). Qed.
Lemma lem3388002 {_88003 _88004 : Type'} (f : _88004 -> _88003) (_35585 : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (_35584 : _88003) : (term225 _88003 _88004 f s P _35584 _35585) = (term217 _88003 _88004 f _35585 s P _35584).
Proof. exact (eq_refl (term225 _88003 _88004 f s P _35584 _35585)). Qed.
Lemma lem3388003 {_88003 _88004 : Type'} (_35585 : _88004) (_35584 : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term217 _88003 _88004 f _35585 s P _35584.
Proof. exact (EQ_MP (@lem3388002 _88003 _88004 f _35585 s P _35584) (@lem3388001 _88003 _88004 _35584 _35585 s P f x h1)). Qed.
Lemma lem3388011 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : P y.
Proof. exact (proj2 (@lem3387905 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388013 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : y = (f x).
Proof. exact (proj1 (@lem3387907 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388026 {_88003 _88004 : Type'} (f : _88004 -> _88003) (_35585 : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (_35584 : _88003) : (term217 _88003 _88004 f _35585 s P _35584) = (term226 _88003 _88004 f _35585 s P _35584).
Proof. exact (@lem3386930 (term227 _88003 _88004 _35584 f _35585) (term228 _88004 _35585 s) (term64 _88003 P _35584)). Qed.
Lemma lem3388027 {_88003 _88004 : Type'} (_35585 : _88004) (_35584 : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term226 _88003 _88004 f _35585 s P _35584.
Proof. exact (EQ_MP (@lem3388026 _88003 _88004 f _35585 s P _35584) (@lem3388003 _88003 _88004 _35585 _35584 s P f x h1)). Qed.
Lemma lem3388059 {_88003 _88004 : Type'} (_35583 : _88004) (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term78 _88003 _88004 s P f _35583.
Proof. exact (EQ_MP (@lem3387996 _88003 _88004 s P f _35583) (@lem3387995 _88003 _88004 _35583 x y s P f h1)). Qed.
Lemma lem3388060 {_88003 : Type'} (P : _88003 -> Prop) : (term229 _88003 P) = (term229 _88003 P).
Proof. exact (eq_refl (term229 _88003 P)). Qed.
Lemma lem3388061 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : (term230 _88003 P y) = (term231 _88003 _88004 P f x).
Proof. exact (MK_COMB (@lem3388060 _88003 P) (@lem3388013 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388062 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term231 _88003 _88004 P f x) = (term79 _88003 _88004 P f x).
Proof. exact (eq_refl (term231 _88003 _88004 P f x)). Qed.
Lemma lem3388063 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (term232 _88003 P y) = (term232 _88003 P y).
Proof. exact (eq_refl (term232 _88003 P y)). Qed.
Lemma lem3388064 {_88003 _88004 : Type'} (y : _88003) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : ((term230 _88003 P y) = (term231 _88003 _88004 P f x)) = ((term230 _88003 P y) = (term79 _88003 _88004 P f x)).
Proof. exact (MK_COMB (@lem3388063 _88003 P y) (@lem3388062 _88003 _88004 P f x)). Qed.
Lemma lem3388065 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (term230 _88003 P y) = (P y).
Proof. exact (eq_refl (term230 _88003 P y)). Qed.
Lemma lem3388066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3388067 {_88003 : Type'} (P : _88003 -> Prop) (y : _88003) : (term232 _88003 P y) = (term233 _88003 P y).
Proof. exact (MK_COMB (@lem3388066) (@lem3388065 _88003 P y)). Qed.
Lemma lem3388068 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term79 _88003 _88004 P f x) = (term79 _88003 _88004 P f x).
Proof. exact (eq_refl (term79 _88003 _88004 P f x)). Qed.
Lemma lem3388069 {_88003 _88004 : Type'} (y : _88003) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : ((term230 _88003 P y) = (term79 _88003 _88004 P f x)) = ((P y) = (term79 _88003 _88004 P f x)).
Proof. exact (MK_COMB (@lem3388067 _88003 P y) (@lem3388068 _88003 _88004 P f x)). Qed.
Lemma lem3388070 {_88003 _88004 : Type'} (y : _88003) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : ((term230 _88003 P y) = (term231 _88003 _88004 P f x)) = ((P y) = (term79 _88003 _88004 P f x)).
Proof. exact (TRANS (@lem3388064 _88003 _88004 y P f x) (@lem3388069 _88003 _88004 y P f x)). Qed.
Lemma lem3388071 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : (P y) = (term79 _88003 _88004 P f x).
Proof. exact (EQ_MP (@lem3388070 _88003 _88004 y P f x) (@lem3388061 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388088 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : @IN _88004 x s.
Proof. exact (proj2 (@lem3387907 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388089 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term234 _88004 x s.
Proof. exact (fun h0 : term228 _88004 x s => @lem3388088 _88003 _88004 x y s P f h1). Qed.
Lemma lem3388091 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3388092 {_88004 : Type'} (x : _88004) (s : _88004 -> Prop) : (term234 _88004 x s) = (@IN _88004 x s).
Proof. exact (@lem3388091 (@IN _88004 x s)). Qed.
Lemma lem3388093 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : @IN _88004 x s.
Proof. exact (EQ_MP (@lem3388092 _88004 x s) (@lem3388089 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388095 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term79 _88003 _88004 P f x.
Proof. exact (EQ_MP (@lem3388071 _88003 _88004 x y s P f h1) (@lem3388011 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388096 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term236 _88003 _88004 P f x.
Proof. exact (fun h0 : term237 _88003 _88004 P f x => @lem3388095 _88003 _88004 x y s P f h1). Qed.
Lemma lem3388098 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3388099 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term236 _88003 _88004 P f x) = (term79 _88003 _88004 P f x).
Proof. exact (@lem3388098 (term79 _88003 _88004 P f x)). Qed.
Lemma lem3388100 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term79 _88003 _88004 P f x.
Proof. exact (EQ_MP (@lem3388099 _88003 _88004 P f x) (@lem3388096 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388102 (a : Prop) (b : Prop) : (term238 a b) = (term239 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3388103 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (_35583 : _88004) : (term78 _88003 _88004 s P f _35583) = (term77 _88003 _88004 s P f _35583).
Proof. exact (@lem3388102 (@IN _88004 _35583 s) (term79 _88003 _88004 P f _35583)). Qed.
Lemma lem3388105 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3388106 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (_35583 : _88004) : (term77 _88003 _88004 s P f _35583) = (term240 _88003 _88004 s P f _35583).
Proof. exact (@lem3388105 (term47 _88003 _88004 s P f _35583)). Qed.
Lemma lem3388107 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (_35583 : _88004) : (term78 _88003 _88004 s P f _35583) = (term240 _88003 _88004 s P f _35583).
Proof. exact (TRANS (@lem3388103 _88003 _88004 s P f _35583) (@lem3388106 _88003 _88004 s P f _35583)). Qed.
Lemma lem3388109 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term47 _88003 _88004 s P f x.
Proof. exact (conj (@lem3388093 _88003 _88004 x y s P f h1) (@lem3388100 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388111 {_88003 _88004 : Type'} (_35583 : _88004) (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term240 _88003 _88004 s P f _35583.
Proof. exact (EQ_MP (@lem3388107 _88003 _88004 s P f _35583) (@lem3388059 _88003 _88004 _35583 x y s P f h1)). Qed.
Lemma lem3388112 {_88003 _88004 : Type'} (_35583 : _88004) (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term240 _88003 _88004 s P f _35583.
Proof. exact (@lem3388111 _88003 _88004 _35583 x y s P f h1). Qed.
Lemma lem3388113 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term240 _88003 _88004 s P f x.
Proof. exact (@lem3388112 _88003 _88004 x x y s P f h1). Qed.
Lemma lem3388116 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : False.
Proof. exact (@lem3388113 _88003 _88004 x y s P f h1 (@lem3388109 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388117 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : term241.
Proof. exact (fun h0 : ~ False => @lem3388116 _88003 _88004 x y s P f h1). Qed.
Lemma lem3388119 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3388120 : term241 = False.
Proof. exact (@lem3388119 False). Qed.
Lemma lem3388168 {_88003 : Type'} (x : _88003) : x = x.
Proof. exact (@lem21386 _88003 x). Qed.
Lemma lem3388169 {_88003 : Type'} (x : _88003) : x = x.
Proof. exact (@lem3388168 _88003 x). Qed.
Lemma lem3388170 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) : (f x) = (f x).
Proof. exact (@lem3388169 _88003 (f x)). Qed.
Lemma lem3388171 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) : term242 _88003 _88004 f x.
Proof. exact (fun h0 : term243 _88003 _88004 f x => @lem3388170 _88003 _88004 f x). Qed.
Lemma lem3388173 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3388174 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) : (term242 _88003 _88004 f x) = ((f x) = (f x)).
Proof. exact (@lem3388173 ((f x) = (f x))). Qed.
Lemma lem3388175 {_88003 _88004 : Type'} (f : _88004 -> _88003) (x : _88004) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3388174 _88003 _88004 f x) (@lem3388171 _88003 _88004 f x)). Qed.
Lemma lem3388177 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : @IN _88004 x s.
Proof. exact (proj1 (@lem3387910 _88003 _88004 s P f x h1)). Qed.
Lemma lem3388178 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term234 _88004 x s.
Proof. exact (fun h0 : term228 _88004 x s => @lem3388177 _88003 _88004 s P f x h1). Qed.
Lemma lem3388180 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3388181 {_88004 : Type'} (x : _88004) (s : _88004 -> Prop) : (term234 _88004 x s) = (@IN _88004 x s).
Proof. exact (@lem3388180 (@IN _88004 x s)). Qed.
Lemma lem3388182 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : @IN _88004 x s.
Proof. exact (EQ_MP (@lem3388181 _88004 x s) (@lem3388178 _88003 _88004 s P f x h1)). Qed.
Lemma lem3388184 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term79 _88003 _88004 P f x.
Proof. exact (proj2 (@lem3387910 _88003 _88004 s P f x h1)). Qed.
Lemma lem3388185 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term236 _88003 _88004 P f x.
Proof. exact (fun h0 : term237 _88003 _88004 P f x => @lem3388184 _88003 _88004 s P f x h1). Qed.
Lemma lem3388187 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3388188 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) : (term236 _88003 _88004 P f x) = (term79 _88003 _88004 P f x).
Proof. exact (@lem3388187 (term79 _88003 _88004 P f x)). Qed.
Lemma lem3388189 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term79 _88003 _88004 P f x.
Proof. exact (EQ_MP (@lem3388188 _88003 _88004 P f x) (@lem3388185 _88003 _88004 s P f x h1)). Qed.
Lemma lem3388191 (a : Prop) (b : Prop) : (term238 a b) = (term239 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3388192 {_88003 _88004 : Type'} (_35585 : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (_35584 : _88003) : (term244 _88003 _88004 _35585 s P _35584) = (term245 _88003 _88004 _35585 s P _35584).
Proof. exact (@lem3388191 (@IN _88004 _35585 s) (P _35584)). Qed.
Lemma lem3388193 {_88003 _88004 : Type'} (_35584 : _88003) (f : _88004 -> _88003) (_35585 : _88004) : (term246 _88003 _88004 _35584 f _35585) = (term246 _88003 _88004 _35584 f _35585).
Proof. exact (eq_refl (term246 _88003 _88004 _35584 f _35585)). Qed.
Lemma lem3388194 {_88003 _88004 : Type'} (f : _88004 -> _88003) (_35585 : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (_35584 : _88003) : (term226 _88003 _88004 f _35585 s P _35584) = (term247 _88003 _88004 f _35585 s P _35584).
Proof. exact (MK_COMB (@lem3388193 _88003 _88004 _35584 f _35585) (@lem3388192 _88003 _88004 _35585 s P _35584)). Qed.
Lemma lem3388196 (a : Prop) (b : Prop) : (term238 a b) = (term239 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3388197 {_88003 _88004 : Type'} (f : _88004 -> _88003) (_35585 : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (_35584 : _88003) : (term247 _88003 _88004 f _35585 s P _35584) = (term248 _88003 _88004 f _35585 s P _35584).
Proof. exact (@lem3388196 (_35584 = (f _35585)) (term249 _88003 _88004 _35585 s P _35584)). Qed.
Lemma lem3388198 {_88003 _88004 : Type'} (f : _88004 -> _88003) (_35585 : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (_35584 : _88003) : (term226 _88003 _88004 f _35585 s P _35584) = (term248 _88003 _88004 f _35585 s P _35584).
Proof. exact (TRANS (@lem3388194 _88003 _88004 f _35585 s P _35584) (@lem3388197 _88003 _88004 f _35585 s P _35584)). Qed.
Lemma lem3388200 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3388201 {_88003 _88004 : Type'} (f : _88004 -> _88003) (_35585 : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (_35584 : _88003) : (term248 _88003 _88004 f _35585 s P _35584) = (term250 _88003 _88004 f _35585 s P _35584).
Proof. exact (@lem3388200 (term251 _88003 _88004 f _35585 s P _35584)). Qed.
Lemma lem3388202 {_88003 _88004 : Type'} (f : _88004 -> _88003) (_35585 : _88004) (s : _88004 -> Prop) (P : _88003 -> Prop) (_35584 : _88003) : (term226 _88003 _88004 f _35585 s P _35584) = (term250 _88003 _88004 f _35585 s P _35584).
Proof. exact (TRANS (@lem3388198 _88003 _88004 f _35585 s P _35584) (@lem3388201 _88003 _88004 f _35585 s P _35584)). Qed.
Lemma lem3388204 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term47 _88003 _88004 s P f x.
Proof. exact (conj (@lem3388182 _88003 _88004 s P f x h1) (@lem3388189 _88003 _88004 s P f x h1)). Qed.
Lemma lem3388205 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term252 _88003 _88004 s P f x.
Proof. exact (conj (@lem3388175 _88003 _88004 f x) (@lem3388204 _88003 _88004 s P f x h1)). Qed.
Lemma lem3388207 {_88003 _88004 : Type'} (_35585 : _88004) (_35584 : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term250 _88003 _88004 f _35585 s P _35584.
Proof. exact (EQ_MP (@lem3388202 _88003 _88004 f _35585 s P _35584) (@lem3388027 _88003 _88004 _35585 _35584 s P f x h1)). Qed.
Lemma lem3388208 {_88003 _88004 : Type'} (_35585 : _88004) (_35584 : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term250 _88003 _88004 f _35585 s P _35584.
Proof. exact (@lem3388207 _88003 _88004 _35585 _35584 s P f x h1). Qed.
Lemma lem3388209 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term253 _88003 _88004 s P f x.
Proof. exact (@lem3388208 _88003 _88004 x (f x) s P f x h1). Qed.
Lemma lem3388212 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : False.
Proof. exact (@lem3388209 _88003 _88004 s P f x h1 (@lem3388205 _88003 _88004 s P f x h1)). Qed.
Lemma lem3388213 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : term241.
Proof. exact (fun h0 : ~ False => @lem3388212 _88003 _88004 s P f x h1). Qed.
Lemma lem3388215 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3388216 : term241 = False.
Proof. exact (@lem3388215 False). Qed.
Lemma lem3388217 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term160 _88003 _88004 s P f x) : False.
Proof. exact (EQ_MP (@lem3388216) (@lem3388213 _88003 _88004 s P f x h1)). Qed.
Lemma lem3388218 {_88003 _88004 : Type'} (x : _88004) (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term144 _88003 _88004 x y s P f) : False.
Proof. exact (EQ_MP (@lem3388120) (@lem3388117 _88003 _88004 x y s P f h1)). Qed.
Lemma lem3388219 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term198 _88003 _88004 y s P f x) : False.
Proof. exact (or_elim (@lem3387901 _88003 _88004 y s P f x h1) (fun h0 : term144 _88003 _88004 x y s P f => @lem3388218 _88003 _88004 x y s P f h0) (fun h0 : term160 _88003 _88004 s P f x => @lem3388217 _88003 _88004 s P f x h0)). Qed.
Lemma lem3388220 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term198 _88003 _88004 y s P f x) : (term198 _88003 _88004 y s P f x) = False.
Proof. exact (prop_ext (fun h2 : term198 _88003 _88004 y s P f x => @lem3388219 _88003 _88004 y s P f x h1) (fun h2 : False => @lem3387901 _88003 _88004 y s P f x h1)). Qed.
Lemma lem3388221 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (x : _88004) (h1 : term198 _88003 _88004 y s P f x) : False.
Proof. exact (EQ_MP (@lem3388220 _88003 _88004 y s P f x h1) (@lem3387901 _88003 _88004 y s P f x h1)). Qed.
Lemma lem3388222 {_88003 _88004 : Type'} (y : _88003) (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term201 _88003 _88004 y s P f) : False.
Proof. exact (ex_elim (@lem3387803 _88003 _88004 y s P f h1) (fun x : _88004 => fun h0 : term200 _88003 _88004 y s P f x => @lem3388221 _88003 _88004 y s P f x h0)). Qed.
Lemma lem3388223 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term52 _88003 _88004 s P f) : False.
Proof. exact (ex_elim (@lem3387802 _88003 _88004 s P f h1) (fun y : _88003 => fun h0 : term202 _88003 _88004 s P f y => @lem3388222 _88003 _88004 y s P f h0)). Qed.
Lemma lem3388224 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term52 _88003 _88004 s P f) : (term52 _88003 _88004 s P f) = False.
Proof. exact (prop_ext (fun h2 : term52 _88003 _88004 s P f => @lem3388223 _88003 _88004 s P f h1) (fun h2 : False => @lem3387277 _88003 _88004 s P f h1)). Qed.
Lemma lem3388225 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) (h1 : term52 _88003 _88004 s P f) : False.
Proof. exact (EQ_MP (@lem3388224 _88003 _88004 s P f h1) (@lem3387277 _88003 _88004 s P f h1)). Qed.
Lemma lem3388226 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : term51 _88003 _88004 s P f.
Proof. exact (fun h0 : term52 _88003 _88004 s P f => @lem3388225 _88003 _88004 s P f h0). Qed.
Lemma lem3388227 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term23 _88003 _88004 f s P) = (term26 _88003 _88004 s P f).
Proof. exact (EQ_MP (@lem3387276 _88003 _88004 s P f) (@lem3388226 _88003 _88004 s P f)). Qed.
Lemma lem3388232 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) : term30 _88003 _88004 P f.
Proof. exact (fun s : _88004 -> Prop => @lem3388227 _88003 _88004 s P f). Qed.
Lemma lem3388237 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term34 _88003 _88004 P.
Proof. exact (fun f : _88004 -> _88003 => @lem3388232 _88003 _88004 P f). Qed.
Lemma lem3388242 {_88003 _88004 : Type'} : term46 _88003 _88004.
Proof. exact (fun P : _88003 -> Prop => @lem3388237 _88003 _88004 P). Qed.
Lemma lem3388243 {_88003 _88004 : Type'} : term45 _88003 _88004.
Proof. exact (EQ_MP (@lem3387272 _88003 _88004) (@lem3388242 _88003 _88004)). Qed.
Lemma lem3388244 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term254 _88003 _88004 P.
Proof. exact (@lem3388243 _88003 _88004 P). Qed.
Lemma lem3388245 {_88003 _88004 : Type'} (P : _88003 -> Prop) : (term254 _88003 _88004 P) = (term36 _88003 _88004 P).
Proof. exact (eq_refl (term254 _88003 _88004 P)). Qed.
Lemma lem3388246 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term36 _88003 _88004 P.
Proof. exact (EQ_MP (@lem3388245 _88003 _88004 P) (@lem3388244 _88003 _88004 P)). Qed.
Lemma lem3388248 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term36 _88003 _88004 P.
Proof. exact (@lem3387027 _88003 _88004 P (@lem3388246 _88003 _88004 P)). Qed.
Lemma lem3388249 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term37 _88003 _88004 P) : False.
Proof. exact (@lem3388248 _88003 _88004 P (@lem3387011 _88003 _88004 P h1)). Qed.
Lemma lem3388250 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term37 _88003 _88004 P) : (term37 _88003 _88004 P) = False.
Proof. exact (prop_ext (fun h2 : term37 _88003 _88004 P => @lem3388249 _88003 _88004 P h1) (fun h2 : False => @lem3387011 _88003 _88004 P h1)). Qed.
Lemma lem3388251 {_88003 _88004 : Type'} (P : _88003 -> Prop) (h1 : term37 _88003 _88004 P) : False.
Proof. exact (EQ_MP (@lem3388250 _88003 _88004 P h1) (@lem3387011 _88003 _88004 P h1)). Qed.
Lemma lem3388252 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term36 _88003 _88004 P.
Proof. exact (fun h0 : term37 _88003 _88004 P => @lem3388251 _88003 _88004 P h0). Qed.
Lemma lem3388253 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term34 _88003 _88004 P.
Proof. exact (EQ_MP (@lem3387010 _88003 _88004 P) (@lem3388252 _88003 _88004 P)). Qed.
Lemma lem3388254 {_88003 _88004 : Type'} (P : _88003 -> Prop) : term33 _88003 _88004 P.
Proof. exact (EQ_MP (@lem3387006 _88003 _88004 P) (@lem3388253 _88003 _88004 P)). Qed.
