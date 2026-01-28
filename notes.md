### Proof Strategy

Consider without multi-language semantics first,

```
Goal: e ⇓ v → ∃ W, W e ⇓ʷ W v
```

What we can show:

```
[Soundness of Collecting Semantics]
e ⇓ v → e ⇓ v, T

[Soundness of Abstract Semantics/Simulation]
e ⇓ᵀ v → ∃ T̃, e ⇓̃ᵀ̃ ṽ ∧ T ⊑ T̃

e ⇓ v, T ∧ e ⇓̃ᵀ̃ ṽ → T ⊑ T̃

[Quotienting Trace Events]
T ⊑ T̃ → ⟦ T ⟧ ⊑ ⟦ T̃ ⟧
```

It suffices to show

```
[Generalization of Annotating with Collecting Semantics/Perfect Analysis]
e ⇓ v, T ∧ ⟦ T ⟧ ⊑ W → W e ⇓ʷ W v
```

Or

```
[Mono] W ⊑ W' ∧ W e ⇓ʷ W v → W' e ⇓ʷ W' v

[Soundness of Annotation with Perfect Analysis] e ⇓ v, T ∧ ⟦ T ⟧ = W → W e ⇓ʷ W v
```

### Linking

Consider the pipeline with known function analysis,

```
           <Ann with K₁>
e₁ ∼>* e₁′      ~>    e₁″ ~>* e₁‴

           <Ann with K₂>
e₂ ∼>* e₂′      ~>    e₂″ ~>* e₂‴

                       <Ann with (K₁ + K₂)?>
(e₁ ⋈ e₂) ~>* (e₁′ ⋈ e₂′)      ~>     (e₁″ ⋈ e₂″) ~>* (e₁‴ ⋈ e₂‴)
```

Note this is incorrect without distinguishing the `K`s.

Instead, we can take advantage of the multi-language semantics.

```
           <injb>  <Ann with K₁> <proj>
e₁ ∼>* e₁′  ->  b₁     ~>    b₁′  ~>  e₁″ ~>* e₁‴

           <injb>  <Ann with K₂> <proj>
e₂ ∼>* e₂′  ->  b₂     ~>    b₁′  ~>  e₂″ ~>* e₂‴

(e₁ ⋈ e₂) ~>* (e₁′ ⋈ e₂′) <unannotated>
          ~>  (b₁ ⋈' b₂) <injb>
          ~>  (b₁′ ⋈' b₂′) <Ann with (K₁ + to_red K₂)>
          ~>  (e₁″ ⋈ e₂″) <proj>
          ~>* (e₁‴ ⋈ e₂‴) <annotated>
where
   (b₁ ⋈' b₂) ≔ red{let x = to_red b₂ in} b₁
```

Note this should generalize to talk about abstract interpretation as well.

### Well-Annotated Terms

Properties
```
* e ⇓ʷ v
* T (E e) ≅ T e
```

Analysis `A` produces well-annotated terms if
```
* A e ⇓ʷ v
* T (E (A e) ≅ T e ≅ T (A e), since E ∘ A = id
```

In terms of linking,
```
e₁ ≈ e₁'

T e₁ ≅ T (A e₁)

e₂ ≈ e₂'

T e₂ ≅ T (A e₂)

(e₁ ⋈ e₂) ≈ (e₁′ ⋈ e₂′)

T (let x = e₂ in e₁) ≅ T (A (let x = e₂ in e₁))

                                  f ↦ w0    f ↦ w0
                                  f w0 ()

                     ≅ T (let x = A e₂ in A e₁)

                                  f ↦ w1    f ↦ w0
                                  f w1 ()
```
