// expect: 2:13 a member may not be named '__proto__'
enum Keys { __proto__ = 'proto', Name = 'name' }
