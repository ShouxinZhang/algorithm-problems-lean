创建精简的lean4题面, 无须解答, 使用sorry占位. 尽可能使用库api来描述核心观念.

正面提示词 (规范要求以及鼓励的行为):

- 开头只需要import Mathlib, 无需import其它任何
- 保持精简的题面风格
- 使用MCP工具寻找准确的库API表达关键定义和定理而不是自己造轮子

负面提示词(需要严格禁止的行为):

- import Mathlib以外的其它库, 例如import Mathlib.Data.List.Basic
- 定义冗余, 陈述冗长
- 明明有库api, 却还是自己造轮子，造成代码严重不规范

使用Lean4 MCP, 结合数学自然语言思考，查询库定理，填充所有sorry完成证明.

正面提示词:

- 最终结果不包含任何sorry或者admit
- 最终结果使用MCP工具确认没有任何报错

负面提示词 (需要严格禁止的行为):

- 使用axiom进行hack
- 修改theorem statement self进行hack （如果定理或者定义的形式化在数学上就是错的，任何修改也都必须要征求用户同意)
- 最终结果有红色波浪线报错
