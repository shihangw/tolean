// expect: 4:9 ordinary readonly classes
// target: ES2021

class C { readonly value: bigint; constructor(value: bigint) { this.value = value; } }
