import json
import os
import copy
import time
import hashlib
import queue
from concurrent.futures import ThreadPoolExecutor
from collections import Counter

class SheepSolver:
    def __init__(self, map_file, num_workers=None):
        # 加载地图数据
        self.map_data = self._load_map_data(map_file)
        
        # 加载中文名称映射
        self.type2name = self._load_type_names()
        
        # 获取所有卡片
        self.all_blocks = self._get_all_blocks()
        self.total_card_counts = Counter(block['type'] for block in self.all_blocks)
        
        # 线程安全的数据结构
        self.task_queue = queue.PriorityQueue()
        self.visited_states = set()
        self.found_solution = False
        self.solution = None
        self.task_counter = 0
        self.output_counter = 0
        self.total_processed = 0
        
        # 线程锁
        self.visited_lock = __import__('threading').Lock()
        self.solution_lock = __import__('threading').Lock()
        self.counter_lock = __import__('threading').Lock()
        self.total_processed_lock = __import__('threading').Lock()
        self.task_counter_lock = __import__('threading').Lock()
        
        # 配置参数
        self.max_depth = 1000  # 最大搜索深度
        self.max_slot_size = 7  # 最大槽位数量
        self.output_interval = 1000  # 进度输出间隔
        
        # 获取可用CPU核心数
        import multiprocessing
        if num_workers is None:
            self.num_workers = multiprocessing.cpu_count()
        else:
            self.num_workers = num_workers
        
        # 预处理地图数据
        self._preprocess_map_data()
        
        # 打印初始信息
        self._print_initial_info()
    
    def _load_map_data(self, map_file):
        """加载地图数据文件"""
        try:
            with open(map_file, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception as e:
            print(f'加载地图数据失败: {e}')
            # 返回默认的示例数据
            return {
                'levelData': {
                    '1': [{'id': 1, 'rowNum': 1, 'rolNum': 1, 'type': 1, 'moldType': 1}]
                }
            }
    
    def _load_type_names(self):
        """加载卡片类型到中文名称的映射"""
        # 这里可以根据实际游戏中的卡片名称进行更新
        return {
            1: "青草", 2: "胡萝卜", 3: "玉米", 4: "树桩", 5: "草叉",
            6: "白菜", 7: "羊毛", 8: "刷子", 9: "剪刀", 10: "奶瓶",
            11: "水桶", 12: "手套", 13: "铃铛", 14: "火堆", 15: "毛球", 16: "干草"
        }
    
    def _preprocess_map_data(self):
        """预处理地图数据，优化搜索性能"""
        # 找出最大层数
        self.max_layer = max(block['layerNum'] for block in self.all_blocks)
    
    def _get_all_blocks(self):
        """获取所有卡片的列表"""
        all_blocks = []
        for layer_key, layer_data in self.map_data['levelData'].items():
            layer_num = int(layer_key)
            for block_data in layer_data:
                try:
                    # 处理可能的字段名称差异
                    row_num = block_data.get('rowNum', block_data.get('row_num', 0))
                    rol_num = block_data.get('rolNum', block_data.get('rol_num', 0))
                    
                    block = {
                        'id': block_data['id'],
                        'rolNum': rol_num,
                        'rowNum': row_num,
                        'layerNum': layer_num,
                        'moldType': block_data.get('moldType', 1),
                        'type': block_data['type']
                    }
                    all_blocks.append(block)
                except Exception as e:
                    print(f'处理卡片数据时出错: {e}, 卡片数据: {block_data}')
        return all_blocks
    
    def _print_initial_info(self):
        """打印初始信息"""
        print(f"求解器初始化完成，准备开始搜索...\n")
    
    def get_clickable_blocks(self, remaining_blocks):
        """高效获取当前可点击的卡片列表"""
        # 直接使用核心实现
        return self._get_clickable_blocks_impl(remaining_blocks)
    
    def _get_clickable_blocks_impl(self, remaining_blocks):
        """获取可点击卡片的核心实现"""
        clickable_blocks = []
        
        # 找出最大层数
        if not remaining_blocks:
            return clickable_blocks
        
        max_layer = max(block['layerNum'] for block in remaining_blocks)
        
        # 首先添加最上层的卡片
        clickable_blocks.extend([block for block in remaining_blocks 
                                if block['layerNum'] == max_layer])
        
        # 然后检查下层卡片是否可点击
        for layer in range(max_layer - 1, 0, -1):
            layer_blocks = [block for block in remaining_blocks if block['layerNum'] == layer]
            upper_blocks = [block for block in remaining_blocks if block['layerNum'] > layer]
            
            for block in layer_blocks:
                if self._is_clickable(block, upper_blocks):
                    clickable_blocks.append(block)
        
        return clickable_blocks
    
    def _is_clickable(self, block, upper_blocks):
        """判断卡片是否可点击"""
        for upper_block in upper_blocks:
            # 根据游戏规则调整碰撞检测的阈值
            if abs(upper_block['rowNum'] - block['rowNum']) < 8 and \
               abs(upper_block['rolNum'] - block['rolNum']) < 8:
                return False
        return True
    
    def _generate_state_key(self, remaining_blocks, slot):
        """生成当前状态的唯一标识"""
        # 获取可点击卡片的类型分布
        clickable_blocks = self.get_clickable_blocks(remaining_blocks)
        clickable_types = Counter(block['type'] for block in clickable_blocks)
        
        # 对槽位进行排序，忽略顺序影响
        sorted_slot = tuple(sorted(slot.items()))
        
        # 对可点击类型进行排序
        sorted_clickable = tuple(sorted(clickable_types.items()))
        
        # 结合剩余卡片数量和卡片类型分布
        remaining_count = len(remaining_blocks)
        remaining_types = Counter(block['type'] for block in remaining_blocks)
        sorted_remaining_types = tuple(sorted(remaining_types.items()))
        
        # 生成MD5哈希值作为状态标识
        state_str = f"{sorted_slot}:{sorted_clickable}:{remaining_count}:{sorted_remaining_types}"
        return hashlib.md5(state_str.encode()).hexdigest()
    
    def _calculate_priority(self, block, slot, remaining_blocks):
        """计算卡片的优先级，用于贪心策略"""
        priority = 0
        
        # 优先级1：如果槽位中已有2个相同类型的卡片，优先选择该类型
        if slot.get(block['type'], 0) == 2:
            priority += 100
        
        # 优先级2：如果槽位中已有该类型卡片，增加优先级
        elif slot.get(block['type'], 0) > 0:
            priority += 50
        
        # 优先级3：如果该类型卡片剩余数量多，增加优先级
        remaining_count = sum(1 for b in remaining_blocks if b['type'] == block['type'])
        if remaining_count >= 3:
            priority += 30
        elif remaining_count == 2:
            priority += 20
        
        # 优先级4：层数较高的卡片优先
        priority += block['layerNum'] * 2
        
        # 优先级5：如果槽位即将填满，优先选择能消除的卡片
        if sum(slot.values()) >= self.max_slot_size - 2:
            if slot.get(block['type'], 0) >= 1:
                priority += 40
        
        return priority
    
    def _process_state(self, remaining_blocks, current_slot, current_seq):
        """处理单个搜索状态"""
        # 检查是否已找到解决方案
        if self.found_solution:
            return False
        
        # 检查深度限制
        if len(current_seq) > self.max_depth:
            return False
        
        # 检查是否通关
        if not remaining_blocks:
            with self.solution_lock:
                if not self.found_solution:
                    self.solution = current_seq
                    self.found_solution = True
                    print(f"找到解决方案！总步数：{len(current_seq)}")
            return True
        
        # 获取可点击卡片
        clickable_blocks = self.get_clickable_blocks(remaining_blocks)
        
        # 如果没有可点击的卡片，此路不通
        if not clickable_blocks:
            with self.total_processed_lock:
                self.total_processed += 1
            return False
        
        # 生成当前状态的标识
        state_key = self._generate_state_key(remaining_blocks, current_slot)
        
        # 检查状态是否已访问
        with self.visited_lock:
            if state_key in self.visited_states:
                with self.total_processed_lock:
                    self.total_processed += 1
                return False
            # 标记状态为已访问
            self.visited_states.add(state_key)
        
        # 使用贪心策略，对可点击卡片进行优先级排序
        prioritized_blocks = sorted(clickable_blocks, 
                                  key=lambda b: self._calculate_priority(b, current_slot, remaining_blocks), 
                                  reverse=True)
        
        # 限制每个状态的分支数量，提高效率
        max_branches = min(5, len(prioritized_blocks))  # 最多尝试5个最高优先级的选择
        
        # 生成新的任务并放入队列
        for i, block in enumerate(prioritized_blocks):
            # 限制分支数量
            if i >= max_branches:
                break
            
            # 如果已找到解决方案，停止处理
            if self.found_solution:
                break
            
            # 复制当前状态
            new_slot = dict(current_slot)  # 转换为普通字典，避免比较问题
            new_remaining_blocks = copy.deepcopy(remaining_blocks)
            new_seq = current_seq.copy()
            
            # 更新槽位
            new_slot[block['type']] = new_slot.get(block['type'], 0) + 1
            
            # 检查槽位是否已满
            if sum(new_slot.values()) > self.max_slot_size:
                continue
            
            # 如果槽位中有3个相同类型的卡片，消除它们
            if new_slot[block['type']] == 3:
                del new_slot[block['type']]
            
            # 从剩余卡片中移除当前卡片
            new_remaining_blocks = [b for b in new_remaining_blocks if b['id'] != block['id']]
            
            # 添加到序列
            new_seq.append(block['id'])
            
            # 计算任务优先级（搜索深度越小优先级越高）
            task_priority = -len(new_seq)  # 负号因为PriorityQueue按升序排列
            
            # 获取唯一计数器，避免比较字典
            with self.task_counter_lock:
                task_id = self.task_counter
                self.task_counter += 1
            
            # 将新任务加入队列，使用task_id作为第二个元素，避免比较字典
            self.task_queue.put((task_priority, task_id, new_remaining_blocks, new_slot, new_seq))
        
        with self.total_processed_lock:
            self.total_processed += 1
        
        # 更新输出计数器
        with self.counter_lock:
            self.output_counter += 1
            if self.output_counter % self.output_interval == 0:
                self._print_progress(remaining_blocks, current_slot, current_seq)
        
        return False
    
    def _print_progress(self, remaining_blocks, current_slot, current_seq):
        """打印当前搜索进度"""
        # 清屏（Windows环境）
        os.system('cls')
        
        # 获取当前序列的中文名
        current_seq_names = []
        for block_id in current_seq:
            block = next((b for b in self.all_blocks if b['id'] == block_id), None)
            if block:
                card_name = self.type2name.get(block['type'], f"类型{block['type']}")
                current_seq_names.append(card_name)
        
        # 格式化序列显示
        seq_display = ", ".join(current_seq_names)  # 显示全部序列
        
        # 格式化卡槽显示
        slot_display = []
        for card_type, count in current_slot.items():
            card_name = self.type2name.get(card_type, f"类型{card_type}")
            slot_display.append(f"{card_name}x{count}")
        
        # 获取线程池和队列状态
        queue_size = self.task_queue.qsize()
        
        # 输出当前状态信息
        print(f"《羊了个羊》并行求解器\n")
        print(f"当前搜索深度: {len(current_seq)}")
        print(f"剩余卡片: {len(remaining_blocks)}")
        print(f"已访问状态: {len(self.visited_states)}")
        print(f"已处理状态: {self.total_processed}")
        print(f"队列大小: {queue_size}")
        print(f"线程数: {self.num_workers}")
        print(f"当前序列: {seq_display}")
        print(f"当前卡槽: {', '.join(slot_display) if slot_display else '空'}")
        print(f"总卡片数: {len(self.all_blocks)}")
        print(f"卡片类型: {len(self.total_card_counts)}种")
        print("\n按Ctrl+C可中断程序")
    
    def _worker(self):
        """工作线程函数"""
        while not self.found_solution:
            try:
                # 从队列获取任务，设置超时以定期检查终止条件
                task = self.task_queue.get(timeout=1.0)
                if task:
                    # 任务格式：(priority, task_id, remaining_blocks, slot, seq)
                    _, _, remaining_blocks, current_slot, current_seq = task
                    
                    # 处理状态
                    try:
                        found = self._process_state(remaining_blocks, current_slot, current_seq)
                        
                        # 标记任务完成 - 只在成功处理后调用
                        self.task_queue.task_done()
                        
                        if found:
                            break
                    except Exception as e:
                        # 即使处理过程中出错，也需要标记任务完成
                        try:
                            self.task_queue.task_done()
                        except ValueError:
                            pass  # 忽略task_done()调用过多的错误
                        print(f"工作线程处理任务出错: {e}")
            except queue.Empty:
                # 队列为空，不调用task_done()
                if self.task_queue.empty():
                    # 等待一小段时间再检查，避免过早退出
                    time.sleep(0.1)
                    if self.task_queue.empty():
                        break
            except Exception as e:
                # 其他异常情况
                print(f"工作线程队列操作出错: {e}")
                # 不调用task_done()，因为我们不确定是否成功获取了任务
    
    def solve(self):
        # 初始状态
        initial_remaining = copy.deepcopy(self.all_blocks)
        initial_slot = dict()  # 使用普通字典
        initial_seq = []
        
        # 获取唯一计数器用于初始任务
        with self.task_counter_lock:
            initial_task_id = self.task_counter
            self.task_counter += 1
        
        # 将初始状态加入队列
        self.task_queue.put((0, initial_task_id, initial_remaining, initial_slot, initial_seq))
        
        # 创建线程池
        with ThreadPoolExecutor(max_workers=self.num_workers) as executor:
            # 提交工作线程任务
            futures = []
            for _ in range(self.num_workers):
                future = executor.submit(self._worker)
                futures.append(future)
            
            try:
                # 等待直到找到解决方案或所有任务完成
                while not self.found_solution:
                    # 检查是否有线程抛出异常
                    active_futures = []
                    for future in futures:
                        if future.running():
                            active_futures.append(future)
                        elif not future.done():
                            active_futures.append(future)
                        else:
                            try:
                                future.result()
                            except Exception as e:
                                print(f"线程执行出错: {e}")
                    
                    # 如果队列为空且没有活跃任务，则搜索完成
                    if self.task_queue.empty() and not active_futures:
                        break
                    
                    # 短暂休眠，避免CPU占用过高
                    time.sleep(0.1)
                    
            except KeyboardInterrupt:
                print("搜索被用户中断")
                self.found_solution = True  # 通知所有线程停止
        
        # 清屏后再显示最终结果
        os.system('cls')
        
        if self.found_solution and self.solution:
            return True
        else:
            print("未找到解决方案")
            return False
    
    def print_solution(self):
        """打印解决方案"""
        if not self.solution:
            print("没有找到解决方案")
            return
        
        print(f"解决方案总步数: {len(self.solution)}")
        
        # 将解决方案保存到文件
        solution_data = {
            "steps": self.solution,
            "step_count": len(self.solution),
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "threads": self.num_workers
        }
        
        try:
            with open('solution.json', 'w', encoding='utf-8') as f:
                json.dump(solution_data, f, ensure_ascii=False, indent=2)
            print("解决方案已保存到solution.json")
        except Exception as e:
            print(f"保存解决方案失败: {e}")

# 使用示例
def main():
    print("《羊了个羊》并行求解器启动...")
    
    # 初始化求解器，使用全部可用CPU核心
    try:
        solver = SheepSolver('map_data.json')
    except Exception as e:
        print(f"初始化失败: {e}")
        return
    
    # 开始求解
    start_time = time.time()
    success = solver.solve()
    end_time = time.time()
    
    # 打印结果
    if success:
        solver.print_solution()
    
    print(f"求解完成，总耗时: {end_time - start_time:.2f}秒")
    print(f"总共访问状态数: {len(solver.visited_states)}")
    print(f"总共处理状态数: {solver.total_processed}")
    print(f"使用的线程数: {solver.num_workers}")

if __name__ == "__main__":
    main()