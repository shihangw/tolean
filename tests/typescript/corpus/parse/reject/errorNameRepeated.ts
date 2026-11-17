// expect: 6:5 an error constructor may assign this.name only once
class E extends Error {
  constructor(label: string) {
    super(label);
    this.name = "First";
    this.name = "Second";
  }
}
