import asyncio
import json
import signal
import logging
import os
import sys
import time
import requests
import argparse
import traceback
import csv
import statistics
import dotenv
from decimal import Decimal
from typing import Tuple
from collections import deque

from lighter.signer_client import SignerClient
import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from exchanges.backpack import BackpackClient
import websockets
from datetime import datetime
import pytz

class Config:
    """Simple config class to wrap dictionary for Backpack client."""
    def __init__(self, config_dict):
        for key, value in config_dict.items():
            setattr(self, key, value)


class HedgeBot:
    """Trading bot that monitors spreads between Backpack and Lighter,
    and places simultaneous market orders on both exchanges when the spread
    exceeds a dynamic threshold (statistical arbitrage / v2 strategy)."""

    def __init__(self, ticker: str, order_quantity: Decimal, fill_timeout: int = 5, max_position: Decimal = Decimal('0')):
        self.ticker = ticker
        self.order_quantity = order_quantity
        self.fill_timeout = fill_timeout
        self.lighter_order_filled = False
        self.current_order = {}
        self.max_position = max_position
        self.spread_history = deque(maxlen=2000)
        self.lighter_size_step = None  # Will be set from market config

        self.exp_backpack_price = 0
        self.exp_lighter_price = 0

        # Initialize logging to file
        os.makedirs("logs", exist_ok=True)
        self.log_filename = f"logs/backpack_{ticker}_hedge_mode_v2_log.txt"
        self.csv_filename = f"logs/backpack_{ticker}_hedge_mode_v2_trades.csv"
        self.bbo_csv_filename = f"logs/backpack_{ticker}_bbo_v2_data.csv"
        self.thresholds_json_filename = f"logs/backpack_{ticker}_thresholds_v2.json"
        self.original_stdout = sys.stdout

        # Initialize CSV file with headers if it doesn't exist
        self._initialize_csv_file()
        self._initialize_bbo_csv_file()

        # Setup logger
        self.logger = logging.getLogger(f"hedge_bot_bp_v2_{ticker}")
        self.logger.setLevel(logging.INFO)

        # Clear any existing handlers to avoid duplicates
        self.logger.handlers.clear()

        # Disable verbose logging from external libraries
        logging.getLogger('urllib3').setLevel(logging.WARNING)
        logging.getLogger('requests').setLevel(logging.WARNING)
        logging.getLogger('websockets').setLevel(logging.WARNING)

        # Disable root logger to prevent INFO:root: messages
        root_logger = logging.getLogger()
        root_logger.setLevel(logging.CRITICAL + 1)
        root_logger.handlers = []
        root_logger.propagate = False

        # Create file handler
        file_handler = logging.FileHandler(self.log_filename)
        file_handler.setLevel(logging.INFO)

        # Create console handler
        console_handler = logging.StreamHandler(sys.stdout)
        console_handler.setLevel(logging.INFO)

        # Create different formatters for file and console
        file_formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        console_formatter = logging.Formatter('%(levelname)s:%(name)s:%(message)s')

        file_handler.setFormatter(file_formatter)
        console_handler.setFormatter(console_formatter)

        # Add handlers to logger
        self.logger.addHandler(file_handler)
        self.logger.addHandler(console_handler)

        # Prevent propagation to root logger to avoid duplicate messages
        self.logger.propagate = False

        # State management
        self.stop_flag = False
        self.order_counter = 0

        # Backpack state
        self.backpack_client = None
        self.backpack_contract_id = None
        self.backpack_tick_size = None
        self.backpack_order_status = None

        # Backpack order book state (using WebSocket)
        self.backpack_order_book = {"bids": {}, "asks": {}}
        self.backpack_best_bid = None
        self.backpack_best_ask = None
        self.backpack_best_bid_size = Decimal('0')
        self.backpack_best_ask_size = Decimal('0')
        self.backpack_order_book_ready = False
        self.backpack_depth_ws_task = None

        # Lighter order book state
        self.lighter_client = None
        self.lighter_order_book = {"bids": {}, "asks": {}}
        self.lighter_best_bid = None
        self.lighter_best_ask = None
        self.lighter_order_book_ready = False
        self.lighter_order_book_offset = 0
        self.lighter_order_book_sequence_gap = False
        self.lighter_snapshot_loaded = False
        self.lighter_order_book_lock = asyncio.Lock()

        # Lighter WebSocket state
        self.lighter_ws_task = None
        self.lighter_order_result = None

        # Lighter order management
        self.lighter_order_status = None
        self.lighter_order_price = None
        self.lighter_order_side = None
        self.lighter_order_size = None
        self.lighter_order_start_time = None

        # Strategy state
        self.waiting_for_lighter_fill = False
        self.wait_start_time = None

        # Order execution tracking
        self.order_execution_complete = False

        # Current order details for immediate execution
        self.current_lighter_price = None
        self.lighter_order_info = None

        # Position tracking
        self.backpack_position = Decimal('0')
        self.lighter_position = Decimal('0')

        # CSV file handles for efficient writing (kept open)
        self.bbo_csv_file = None
        self.bbo_csv_writer = None
        self.bbo_write_counter = 0
        self.bbo_flush_interval = 10  # Flush every N writes

        # Trading statistics tracking
        self.session_start_time = time.time()
        self.last_summary_time = time.time()
        self.summary_interval = 300  # Default: print summary every 5 minutes

        # Max position threshold relaxation tracking
        self.at_max_position_since = None  # Timestamp when position first hit max
        self.threshold_relax_start = 1800     # Start relaxing after N seconds at max (default: 1800s)
        self.threshold_relax_rate = Decimal('0.0000002')  # Relax threshold by this per second
        self.threshold_relax_cap = Decimal('0.00006')    # Maximum relaxation (price * cap), conservative to preserve arb edge

        # Backpack trade stats
        self.bp_trade_count = 0
        self.bp_buy_count = 0
        self.bp_sell_count = 0
        self.bp_buy_volume_base = Decimal('0')   # Total base amount bought
        self.bp_sell_volume_base = Decimal('0')  # Total base amount sold
        self.bp_buy_cost_quote = Decimal('0')    # Total quote spent on buys (qty * price)
        self.bp_sell_revenue_quote = Decimal('0') # Total quote received from sells (qty * price)

        # Lighter trade stats
        self.lt_trade_count = 0
        self.lt_buy_count = 0
        self.lt_sell_count = 0
        self.lt_buy_volume_base = Decimal('0')
        self.lt_sell_volume_base = Decimal('0')
        self.lt_buy_cost_quote = Decimal('0')
        self.lt_sell_revenue_quote = Decimal('0')

        # Account balance tracking (updated in periodic summary)
        self.bp_balance = None   # Backpack account total balance (USDC)
        self.lt_balance = None   # Lighter account collateral (USDC)

        # Lighter API configuration
        self.lighter_base_url = "https://mainnet.zklighter.elliot.ai"
        self.account_index = int(os.getenv('LIGHTER_ACCOUNT_INDEX'))
        self.api_key_index = int(os.getenv('LIGHTER_API_KEY_INDEX'))

        # Backpack configuration
        self.backpack_public_key = os.getenv('BACKPACK_PUBLIC_KEY')
        self.backpack_secret_key = os.getenv('BACKPACK_SECRET_KEY')

    def shutdown(self, signum=None, frame=None):
        """Synchronous shutdown handler (called by signal handler)."""
        # Just set the stop flag - actual cleanup happens in async_shutdown()
        self.stop_flag = True

    async def async_shutdown(self):
        """Async shutdown handler for proper cleanup."""
        self.stop_flag = True
        self.logger.info("\n🛑 Stopping...")

        # Cancel Lighter WebSocket task
        if self.lighter_ws_task and not self.lighter_ws_task.done():
            try:
                self.lighter_ws_task.cancel()
                await asyncio.sleep(0.1)
                self.logger.info("🔌 Lighter WebSocket task cancelled")
            except Exception as e:
                self.logger.error(f"Error cancelling Lighter WebSocket task: {e}")

        # Cancel Backpack depth WebSocket task
        if self.backpack_depth_ws_task and not self.backpack_depth_ws_task.done():
            try:
                self.backpack_depth_ws_task.cancel()
                await asyncio.sleep(0.1)
                self.logger.info("🔌 Backpack depth WebSocket task cancelled")
            except Exception as e:
                self.logger.error(f"Error cancelling Backpack depth WebSocket task: {e}")

        # Disconnect Backpack WebSocket properly
        if self.backpack_client and hasattr(self.backpack_client, 'ws_manager') and self.backpack_client.ws_manager:
            try:
                await asyncio.wait_for(self.backpack_client.disconnect(), timeout=2.0)
                self.logger.info("🔌 Backpack WebSocket disconnected")
            except (asyncio.TimeoutError, RuntimeError, Exception) as e:
                pass

        # Close CSV file handles
        if self.bbo_csv_file:
            try:
                self.bbo_csv_file.flush()
                self.bbo_csv_file.close()
                self.logger.info("📊 BBO CSV file closed")
            except Exception as e:
                self.logger.error(f"Error closing BBO CSV file: {e}")

        # Close logging handlers properly
        for handler in self.logger.handlers[:]:
            try:
                handler.close()
                self.logger.removeHandler(handler)
            except Exception:
                pass

    def _initialize_csv_file(self):
        """Initialize CSV file with headers if it doesn't exist."""
        if not os.path.exists(self.csv_filename):
            with open(self.csv_filename, 'w', newline='') as csvfile:
                writer = csv.writer(csvfile)
                writer.writerow(['exchange', 'timestamp', 'side', 'price', 'quantity', 'expected_price'])

    def _initialize_bbo_csv_file(self):
        """Initialize BBO CSV file with headers if it doesn't exist."""
        file_exists = os.path.exists(self.bbo_csv_filename)

        # Open file in append mode (will create if doesn't exist)
        self.bbo_csv_file = open(self.bbo_csv_filename, 'a', newline='', buffering=8192)
        self.bbo_csv_writer = csv.writer(self.bbo_csv_file)

        # Write header only if file is new
        if not file_exists:
            self.bbo_csv_writer.writerow([
                'timestamp',
                'backpack_bid',
                'backpack_ask',
                'lighter_bid',
                'lighter_ask',
                'long_bp_spread',
                'short_bp_spread',
                'long_bp',
                'short_bp'
            ])
            self.bbo_csv_file.flush()

    def print_periodic_summary(self, force: bool = False):
        """Print periodic trading summary with volume and P&L stats."""
        now = time.time()
        if not force and (now - self.last_summary_time) < self.summary_interval:
            return
        self.last_summary_time = now

        elapsed = now - self.session_start_time
        hours = int(elapsed // 3600)
        minutes = int((elapsed % 3600) // 60)
        seconds = int(elapsed % 60)
        runtime_str = f"{hours}h {minutes}m {seconds}s"

        # Calculate volumes in quote (USDT)
        bp_total_volume = self.bp_buy_cost_quote + self.bp_sell_revenue_quote
        lt_total_volume = self.lt_buy_cost_quote + self.lt_sell_revenue_quote
        combined_volume = bp_total_volume + lt_total_volume

        # Calculate realized P&L per exchange (only matched portion counts)
        # Realized = matched_qty * (avg_sell_price - avg_buy_price)
        # Unmatched portion is unrealized (open position from trades)
        bp_realized_pnl = Decimal('0')
        if self.bp_buy_volume_base > 0 and self.bp_sell_volume_base > 0:
            matched_qty = min(self.bp_buy_volume_base, self.bp_sell_volume_base)
            avg_buy = self.bp_buy_cost_quote / self.bp_buy_volume_base
            avg_sell = self.bp_sell_revenue_quote / self.bp_sell_volume_base
            bp_realized_pnl = matched_qty * (avg_sell - avg_buy)

        lt_realized_pnl = Decimal('0')
        if self.lt_buy_volume_base > 0 and self.lt_sell_volume_base > 0:
            matched_qty = min(self.lt_buy_volume_base, self.lt_sell_volume_base)
            avg_buy = self.lt_buy_cost_quote / self.lt_buy_volume_base
            avg_sell = self.lt_sell_revenue_quote / self.lt_sell_volume_base
            lt_realized_pnl = matched_qty * (avg_sell - avg_buy)

        # Combined realized P&L across both exchanges (hedging pair P&L)
        # For a hedging bot: buy on one exchange, sell on the other
        # Combined realized = matched_qty * (avg_sell_all - avg_buy_all)
        total_buy_base = self.bp_buy_volume_base + self.lt_buy_volume_base
        total_sell_base = self.bp_sell_volume_base + self.lt_sell_volume_base
        total_buy_cost = self.bp_buy_cost_quote + self.lt_buy_cost_quote
        total_sell_revenue = self.bp_sell_revenue_quote + self.lt_sell_revenue_quote

        combined_realized_pnl = Decimal('0')
        if total_buy_base > 0 and total_sell_base > 0:
            matched_qty = min(total_buy_base, total_sell_base)
            avg_buy_all = total_buy_cost / total_buy_base
            avg_sell_all = total_sell_revenue / total_sell_base
            combined_realized_pnl = matched_qty * (avg_sell_all - avg_buy_all)

        # Unrealized P&L based on current positions and mid prices
        bp_unrealized = Decimal('0')
        lt_unrealized = Decimal('0')
        if self.backpack_best_bid and self.backpack_best_ask:
            bp_mid = (self.backpack_best_bid + self.backpack_best_ask) / 2
            bp_unrealized = self.backpack_position * bp_mid
        if self.lighter_best_bid and self.lighter_best_ask:
            lt_mid = (self.lighter_best_bid + self.lighter_best_ask) / 2
            lt_unrealized = self.lighter_position * lt_mid

        total_unrealized = bp_unrealized + lt_unrealized
        # Estimated total P&L = combined realized + unrealized
        estimated_pnl = combined_realized_pnl + total_unrealized

        total_trades = self.bp_trade_count + self.lt_trade_count

        # Fetch account balances
        self.bp_balance = self.get_backpack_balance()
        self.lt_balance = self.get_lighter_balance()

        self.logger.info("="*60)
        self.logger.info(f"📊 定时交易总结 | 运行时间: {runtime_str}")
        self.logger.info("-"*60)
        self.logger.info(f"📈 Backpack:  交易 {self.bp_trade_count} 笔 (买 {self.bp_buy_count} / 卖 {self.bp_sell_count})")
        self.logger.info(f"   买入量: {self.bp_buy_volume_base} {self.ticker} | 卖出量: {self.bp_sell_volume_base} {self.ticker}")
        self.logger.info(f"   买入额: {self.bp_buy_cost_quote:.2f} USDT | 卖出额: {self.bp_sell_revenue_quote:.2f} USDT")
        self.logger.info(f"   交易额: {bp_total_volume:.2f} USDT | 已实现盈亏: {bp_realized_pnl:+.4f} USDT")
        self.logger.info("-"*60)
        self.logger.info(f"📈 Lighter:   交易 {self.lt_trade_count} 笔 (买 {self.lt_buy_count} / 卖 {self.lt_sell_count})")
        self.logger.info(f"   买入量: {self.lt_buy_volume_base} {self.ticker} | 卖出量: {self.lt_sell_volume_base} {self.ticker}")
        self.logger.info(f"   买入额: {self.lt_buy_cost_quote:.2f} USDT | 卖出额: {self.lt_sell_revenue_quote:.2f} USDT")
        self.logger.info(f"   交易额: {lt_total_volume:.2f} USDT | 已实现盈亏: {lt_realized_pnl:+.4f} USDT")
        self.logger.info("-"*60)
        self.logger.info(f"💰 合计: 交易 {total_trades} 笔 | 总交易额: {combined_volume:.2f} USDT")
        self.logger.info(f"   跨所对冲已实现盈亏: {combined_realized_pnl:+.4f} USDT")
        self.logger.info(f"   未实现盈亏: {total_unrealized:+.4f} USDT (BP仓位: {self.backpack_position} | LT仓位: {self.lighter_position})")
        self.logger.info(f"   估计总盈亏: {estimated_pnl:+.4f} USDT")
        self.logger.info("-"*60)
        bp_bal_str = f"{self.bp_balance:.2f} USDC" if self.bp_balance and self.bp_balance >= 0 else "获取失败"
        lt_bal_str = f"{self.lt_balance:.2f} USDC" if self.lt_balance and self.lt_balance >= 0 else "获取失败"
        total_bal_str = ""
        if self.bp_balance and self.bp_balance >= 0 and self.lt_balance and self.lt_balance >= 0:
            total_bal_str = f" | 合计: {self.bp_balance + self.lt_balance:.2f} USDC"
        self.logger.info(f"💎 账户资金: BP: {bp_bal_str} | LT: {lt_bal_str}{total_bal_str}")
        self.logger.info("="*60)

    def log_trade_to_csv(self, exchange: str, side: str, price: str, quantity: str, expected_price: str):
        """Log trade details to CSV file."""
        timestamp = datetime.now(pytz.UTC).isoformat()

        with open(self.csv_filename, 'a', newline='') as csvfile:
            writer = csv.writer(csvfile)
            writer.writerow([
                exchange,
                timestamp,
                side,
                price,
                quantity,
                expected_price
            ])

        self.logger.info(f"📊 Trade logged to CSV: {exchange} {side} {quantity} @ {price}")

    def log_bbo_to_csv(self, bp_bid: Decimal, bp_ask: Decimal, lighter_bid: Decimal, lighter_ask: Decimal, long_bp: bool, short_bp: bool):
        """Log BBO data to CSV file using buffered writes."""
        if not self.bbo_csv_file or not self.bbo_csv_writer:
            self._initialize_bbo_csv_file()

        timestamp = datetime.now(pytz.UTC).isoformat()

        # Calculate spreads
        long_bp_spread = lighter_bid - bp_bid if lighter_bid and lighter_bid > 0 and bp_bid > 0 else Decimal('0')
        short_bp_spread = bp_ask - lighter_ask if bp_ask > 0 and lighter_ask and lighter_ask > 0 else Decimal('0')

        try:
            self.bbo_csv_writer.writerow([
                timestamp,
                float(bp_bid),
                float(bp_ask),
                float(lighter_bid) if lighter_bid and lighter_bid > 0 else 0.0,
                float(lighter_ask) if lighter_ask and lighter_ask > 0 else 0.0,
                float(long_bp_spread),
                float(short_bp_spread),
                long_bp,
                short_bp
            ])

            # Increment counter and flush periodically
            self.bbo_write_counter += 1
            if self.bbo_write_counter >= self.bbo_flush_interval:
                self.bbo_csv_file.flush()
                self.bbo_write_counter = 0
        except Exception as e:
            self.logger.error(f"Error writing to BBO CSV: {e}")
            try:
                if self.bbo_csv_file:
                    self.bbo_csv_file.close()
            except Exception:
                pass
            self._initialize_bbo_csv_file()

    def log_thresholds_to_json(self, long_bp_threshold: Decimal, short_bp_threshold: Decimal):
        """Log threshold values to JSON file."""
        try:
            timestamp = datetime.now(pytz.UTC).isoformat()
            thresholds_data = {
                "timestamp": timestamp,
                "long_bp_threshold": float(long_bp_threshold),
                "short_bp_threshold": float(short_bp_threshold)
            }
            with open(self.thresholds_json_filename, 'w') as json_file:
                json.dump(thresholds_data, json_file, indent=2)
        except Exception as e:
            self.logger.error(f"Error writing thresholds to JSON: {e}")

    def handle_lighter_order_result(self, order_data):
        """Handle Lighter order result from WebSocket."""
        try:
            filled_base = Decimal(order_data["filled_base_amount"])
            filled_quote = Decimal(order_data["filled_quote_amount"])
            order_data["avg_filled_price"] = filled_quote / filled_base
            if order_data["is_ask"]:
                order_data["side"] = "SHORT"
                order_type = "OPEN"
                self.lighter_position -= filled_base
                # Track Lighter sell stats
                self.lt_trade_count += 1
                self.lt_sell_count += 1
                self.lt_sell_volume_base += filled_base
                self.lt_sell_revenue_quote += filled_quote
            else:
                order_data["side"] = "LONG"
                order_type = "CLOSE"
                self.lighter_position += filled_base
                # Track Lighter buy stats
                self.lt_trade_count += 1
                self.lt_buy_count += 1
                self.lt_buy_volume_base += filled_base
                self.lt_buy_cost_quote += filled_quote

            client_order_index = order_data["client_order_id"]

            self.logger.info(f"[{client_order_index}] [{order_type}] [Lighter] [FILLED]: "
                             f"{order_data['filled_base_amount']} @ {order_data['avg_filled_price']}")

            # Log Lighter trade to CSV
            self.log_trade_to_csv(
                exchange='Lighter',
                side=order_data['side'],
                price=str(order_data['avg_filled_price']),
                quantity=str(order_data['filled_base_amount']),
                expected_price=str(self.exp_lighter_price)
            )

            # Mark execution as complete
            self.lighter_order_filled = True
            self.order_execution_complete = True

        except Exception as e:
            self.logger.error(f"Error handling Lighter order result: {e}")

    async def reset_lighter_order_book(self):
        """Reset Lighter order book state."""
        async with self.lighter_order_book_lock:
            self.lighter_order_book["bids"].clear()
            self.lighter_order_book["asks"].clear()
            self.lighter_order_book_offset = 0
            self.lighter_order_book_sequence_gap = False
            self.lighter_snapshot_loaded = False
            self.lighter_best_bid = None
            self.lighter_best_ask = None

    def update_lighter_order_book(self, side: str, levels: list):
        """Update Lighter order book with new levels."""
        for level in levels:
            if isinstance(level, list) and len(level) >= 2:
                price = Decimal(level[0])
                size = Decimal(level[1])
            elif isinstance(level, dict):
                price = Decimal(level.get("price", 0))
                size = Decimal(level.get("size", 0))
            else:
                self.logger.warning(f"⚠️ Unexpected level format: {level}")
                continue

            if size > 0:
                self.lighter_order_book[side][price] = size
            else:
                self.lighter_order_book[side].pop(price, None)

    def validate_order_book_offset(self, new_offset: int) -> bool:
        """Validate order book offset sequence."""
        if new_offset <= self.lighter_order_book_offset:
            self.logger.warning(
                f"⚠️ Out-of-order update: new_offset={new_offset}, current_offset={self.lighter_order_book_offset}")
            return False
        return True

    def validate_order_book_integrity(self) -> bool:
        """Validate order book integrity."""
        for side in ["bids", "asks"]:
            for price, size in self.lighter_order_book[side].items():
                if price <= 0 or size <= 0:
                    self.logger.error(f"❌ Invalid order book data: {side} price={price}, size={size}")
                    return False
        return True

    def get_lighter_best_levels(self) -> Tuple[Tuple[Decimal, Decimal], Tuple[Decimal, Decimal]]:
        """Get best bid and ask levels from Lighter order book.
        Filters levels with notional value >= 4000 to avoid thin liquidity."""
        best_bid = None
        best_ask = None

        if self.lighter_order_book["bids"]:
            bid_levels = [(price, size) for price, size in self.lighter_order_book["bids"].items()
                if size * price >= 4000]
            best_bid = max(bid_levels) if bid_levels else (None, None)

        if self.lighter_order_book["asks"]:
            ask_levels = [(price, size) for price, size in self.lighter_order_book["asks"].items()
                if size * price >= 4000]
            best_ask = min(ask_levels) if ask_levels else (None, None)

        return best_bid, best_ask

    def get_lighter_order_price(self, is_ask: bool) -> Decimal:
        """Get order price from Lighter order book."""
        best_bid, best_ask = self.get_lighter_best_levels()

        if best_bid is None or best_ask is None:
            raise Exception("Cannot calculate order price - missing order book data")

        if is_ask:
            order_price = best_bid[0] + self.tick_size
        else:
            order_price = best_ask[0] - self.tick_size

        return order_price

    def calculate_adjusted_price(self, original_price: Decimal, side: str, adjustment_percent: Decimal) -> Decimal:
        """Calculate adjusted price for order modification."""
        adjustment = original_price * adjustment_percent

        if side.lower() == 'buy':
            return original_price + adjustment
        else:
            return original_price - adjustment

    async def request_fresh_snapshot(self, ws):
        """Request fresh order book snapshot."""
        await ws.send(json.dumps({"type": "subscribe", "channel": f"order_book/{self.lighter_market_index}"}))

    async def handle_lighter_ws(self):
        """Handle Lighter WebSocket connection and messages."""
        url = "wss://mainnet.zklighter.elliot.ai/stream"
        cleanup_counter = 0

        while not self.stop_flag:
            timeout_count = 0
            try:
                # Reset order book state before connecting
                await self.reset_lighter_order_book()

                async with websockets.connect(url) as ws:
                    # Subscribe to order book updates
                    await ws.send(json.dumps({"type": "subscribe", "channel": f"order_book/{self.lighter_market_index}"}))

                    # Subscribe to account orders updates
                    account_orders_channel = f"account_orders/{self.lighter_market_index}/{self.account_index}"

                    # Get auth token for the subscription
                    try:
                        auth_token, err = self.lighter_client.create_auth_token_with_expiry(api_key_index=self.api_key_index)
                        if err is not None:
                            self.logger.warning(f"⚠️ Failed to create auth token for account orders subscription: {err}")
                        else:
                            auth_message = {
                                "type": "subscribe",
                                "channel": account_orders_channel,
                                "auth": auth_token
                            }
                            await ws.send(json.dumps(auth_message))
                            self.logger.info("✅ Subscribed to account orders with auth token (expires in 10 minutes)")
                    except Exception as e:
                        self.logger.warning(f"⚠️ Error creating auth token for account orders subscription: {e}")

                    while not self.stop_flag:
                        try:
                            msg = await asyncio.wait_for(ws.recv(), timeout=1)

                            try:
                                data = json.loads(msg)
                            except json.JSONDecodeError as e:
                                self.logger.warning(f"⚠️ JSON parsing error in Lighter websocket: {e}")
                                continue

                            # Reset timeout counter on successful message
                            timeout_count = 0

                            async with self.lighter_order_book_lock:
                                if data.get("type") == "subscribed/order_book":
                                    # Initial snapshot
                                    self.lighter_order_book["bids"].clear()
                                    self.lighter_order_book["asks"].clear()

                                    order_book = data.get("order_book", {})
                                    if order_book and "offset" in order_book:
                                        self.lighter_order_book_offset = order_book["offset"]
                                        self.logger.info(f"✅ Initial order book offset set to: {self.lighter_order_book_offset}")

                                    bids = order_book.get("bids", [])
                                    asks = order_book.get("asks", [])

                                    self.update_lighter_order_book("bids", bids)
                                    self.update_lighter_order_book("asks", asks)
                                    self.lighter_snapshot_loaded = True
                                    self.lighter_order_book_ready = True

                                    self.logger.info(f"✅ Lighter order book snapshot loaded with "
                                                     f"{len(self.lighter_order_book['bids'])} bids and "
                                                     f"{len(self.lighter_order_book['asks'])} asks")

                                elif data.get("type") == "update/order_book" and self.lighter_snapshot_loaded:
                                    order_book = data.get("order_book", {})
                                    if not order_book or "offset" not in order_book:
                                        self.logger.warning("⚠️ Order book update missing offset, skipping")
                                        continue

                                    new_offset = order_book["offset"]

                                    if not self.validate_order_book_offset(new_offset):
                                        self.lighter_order_book_sequence_gap = True
                                        break

                                    self.lighter_order_book_offset = new_offset
                                    self.update_lighter_order_book("bids", order_book.get("bids", []))
                                    self.update_lighter_order_book("asks", order_book.get("asks", []))

                                    if not self.validate_order_book_integrity():
                                        self.logger.warning("🔄 Order book integrity check failed, requesting fresh snapshot...")
                                        break

                                    best_bid, best_ask = self.get_lighter_best_levels()

                                    if best_bid is not None:
                                        self.lighter_best_bid = best_bid[0]
                                    if best_ask is not None:
                                        self.lighter_best_ask = best_ask[0]

                                elif data.get("type") == "ping":
                                    await ws.send(json.dumps({"type": "pong"}))
                                elif data.get("type") == "update/account_orders":
                                    orders = data.get("orders", {}).get(str(self.lighter_market_index), [])
                                    for order in orders:
                                        if order.get("status") == "filled":
                                            self.handle_lighter_order_result(order)
                                elif data.get("type") == "update/order_book" and not self.lighter_snapshot_loaded:
                                    continue

                            # Periodic cleanup
                            cleanup_counter += 1
                            if cleanup_counter >= 1000:
                                cleanup_counter = 0

                            if self.lighter_order_book_sequence_gap:
                                try:
                                    await self.request_fresh_snapshot(ws)
                                    self.lighter_order_book_sequence_gap = False
                                except Exception as e:
                                    self.logger.error(f"⚠️ Failed to request fresh snapshot: {e}")
                                    break

                        except asyncio.TimeoutError:
                            timeout_count += 1
                            if timeout_count % 3 == 0:
                                self.logger.warning(f"⏰ No message from Lighter websocket for {timeout_count} seconds")
                            continue
                        except websockets.exceptions.ConnectionClosed as e:
                            self.logger.warning(f"⚠️ Lighter websocket connection closed: {e}")
                            break
                        except websockets.exceptions.WebSocketException as e:
                            self.logger.warning(f"⚠️ Lighter websocket error: {e}")
                            break
                        except Exception as e:
                            self.logger.error(f"⚠️ Error in Lighter websocket: {e}")
                            self.logger.error(f"⚠️ Full traceback: {traceback.format_exc()}")
                            break
            except Exception as e:
                self.logger.error(f"⚠️ Failed to connect to Lighter websocket: {e}")

            # Wait before reconnecting
            await asyncio.sleep(2)

    def setup_signal_handlers(self):
        """Setup signal handlers for graceful shutdown."""
        def signal_handler(signum, frame):
            """Handle shutdown signals by setting stop flag."""
            self.stop_flag = True
            self.logger.info("\n🛑 Received interrupt signal (Ctrl+C)...")

        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)

    def initialize_lighter_client(self):
        """Initialize the Lighter client."""
        if self.lighter_client is None:
            api_key_private_key = os.getenv('API_KEY_PRIVATE_KEY')
            if not api_key_private_key:
                raise Exception("API_KEY_PRIVATE_KEY environment variable not set")

            self.lighter_client = SignerClient(
                url=self.lighter_base_url,
                account_index=self.account_index,
                api_private_keys={self.api_key_index: api_key_private_key}
            )

            err = self.lighter_client.check_client()
            if err is not None:
                raise Exception(f"CheckClient error: {err}")

            self.logger.info("✅ Lighter client initialized successfully")
        return self.lighter_client

    def initialize_backpack_client(self):
        """Initialize the Backpack client."""
        if not self.backpack_public_key or not self.backpack_secret_key:
            raise ValueError("BACKPACK_PUBLIC_KEY and BACKPACK_SECRET_KEY must be set in environment variables")

        # Create config for Backpack client
        config_dict = {
            'ticker': self.ticker,
            'contract_id': '',  # Will be set when we get contract info
            'quantity': self.order_quantity,
            'tick_size': Decimal('0.01'),  # Will be updated when we get contract info
            'close_order_side': 'sell'  # Default
        }

        config = Config(config_dict)
        self.backpack_client = BackpackClient(config)

        self.logger.info("✅ Backpack client initialized successfully")
        return self.backpack_client

    def get_lighter_market_config(self) -> Tuple[int, int, int, Decimal]:
        """Get Lighter market configuration."""
        url = f"{self.lighter_base_url}/api/v1/orderBooks"
        headers = {"accept": "application/json"}

        try:
            response = requests.get(url, headers=headers, timeout=10)
            response.raise_for_status()

            if not response.text.strip():
                raise Exception("Empty response from Lighter API")

            data = response.json()

            if "order_books" not in data:
                raise Exception("Unexpected response format")

            for market in data["order_books"]:
                if market["symbol"] == self.ticker:
                    size_decimals = market["supported_size_decimals"]
                    price_decimals = market["supported_price_decimals"]
                    price_multiplier = pow(10, price_decimals)
                    base_amount_multiplier = pow(10, size_decimals)
                    tick_size = Decimal("1") / (Decimal("10") ** price_decimals)
                    # Size step: minimum increment for base amount
                    size_step = Decimal("1") / (Decimal("10") ** size_decimals)
                    self.lighter_size_step = size_step
                    self.logger.info(f"Lighter market config: size_decimals={size_decimals}, "
                                     f"price_decimals={price_decimals}, size_step={size_step}")
                    return (market["market_id"],
                           base_amount_multiplier,
                           price_multiplier,
                           tick_size
                           )
            raise Exception(f"Ticker {self.ticker} not found")

        except Exception as e:
            self.logger.error(f"⚠️ Error getting market config: {e}")
            raise

    async def get_backpack_contract_info(self) -> Tuple[str, Decimal]:
        """Get Backpack contract ID and tick size."""
        if not self.backpack_client:
            raise Exception("Backpack client not initialized")

        contract_id, tick_size = await self.backpack_client.get_contract_attributes()

        if self.order_quantity < self.backpack_client.config.quantity:
            raise ValueError(
                f"Order quantity is less than min quantity: {self.order_quantity} < {self.backpack_client.config.quantity}")

        return contract_id, tick_size

    async def get_backpack_position(self) -> Decimal:
        """Get Backpack position."""
        if not self.backpack_client:
            raise Exception("Backpack client not initialized")

        return await self.backpack_client.get_account_positions()

    def round_to_tick(self, price: Decimal) -> Decimal:
        """Round price to tick size."""
        if self.backpack_tick_size is None:
            return price
        return (price / self.backpack_tick_size).quantize(Decimal('1')) * self.backpack_tick_size

    async def place_backpack_market_order(self, side: str, quantity: Decimal):
        """Place a market order on Backpack."""
        if not self.backpack_client:
            raise Exception("Backpack client not initialized")
        self.backpack_order_status = None

        return await self.backpack_client.place_market_order(self.backpack_contract_id, quantity, side.lower())

    async def place_lighter_market_order(self, lighter_side: str, quantity: Decimal):
        """Place a market order on Lighter."""
        if not self.lighter_client:
            self.initialize_lighter_client()

        best_bid, best_ask = self.get_lighter_best_levels()

        if best_bid is None or best_ask is None:
            self.logger.error("❌ Cannot place Lighter order - missing order book data")
            return None

        # Determine order parameters
        if lighter_side.lower() == 'buy':
            order_type = "CLOSE"
            is_ask = False
            price = best_ask[0] * Decimal('1.002')
        else:
            order_type = "OPEN"
            is_ask = True
            price = best_bid[0] * Decimal('0.998')

        # Reset order state
        self.lighter_order_filled = False
        self.lighter_order_price = price
        self.lighter_order_side = lighter_side
        self.lighter_order_size = quantity

        try:
            # Round quantity to Lighter's size step to avoid precision issues
            if hasattr(self, 'lighter_size_step') and self.lighter_size_step:
                quantity = (quantity / self.lighter_size_step).to_integral_value() * self.lighter_size_step

            base_amount = round(float(quantity * self.base_amount_multiplier))
            price_int = round(float(price * self.price_multiplier))

            if base_amount <= 0:
                self.logger.error(f"❌ Invalid base_amount={base_amount} (quantity={quantity}, multiplier={self.base_amount_multiplier})")
                return None

            self.logger.info(f"Lighter order params: qty={quantity}, base_amount={base_amount}, price_int={price_int}")

            client_order_index = int(time.time() * 1000)
            tx, tx_hash, error = await self.lighter_client.create_order(
                market_index=self.lighter_market_index,
                client_order_index=client_order_index,
                base_amount=base_amount,
                price=price_int,
                is_ask=is_ask,
                order_type=self.lighter_client.ORDER_TYPE_LIMIT,
                time_in_force=self.lighter_client.ORDER_TIME_IN_FORCE_GOOD_TILL_TIME,
                reduce_only=False,
                trigger_price=0,
            )
            if error is not None:
                raise Exception(f"Error placing Lighter order: {error}")

            self.logger.info(f"[{client_order_index}] [{order_type}] [Lighter] [OPEN]: {quantity}")

            await self.monitor_lighter_order(client_order_index)

            return tx_hash
        except Exception as e:
            self.logger.error(f"❌ Error placing Lighter order: {e}")
            return None

    async def monitor_lighter_order(self, client_order_index: int):
        """Monitor Lighter order and wait for fill."""
        start_time = time.time()
        while not self.lighter_order_filled and not self.stop_flag:
            if time.time() - start_time > 30:
                self.logger.error(f"❌ Timeout waiting for Lighter order fill after {time.time() - start_time:.1f}s")
                self.logger.error(f"❌ Order state - Filled: {self.lighter_order_filled}")

                self.logger.warning("⚠️ Using fallback - marking order as filled to continue trading")
                self.lighter_order_filled = True
                self.waiting_for_lighter_fill = False
                self.order_execution_complete = True
                break

            await asyncio.sleep(0.1)

    async def modify_lighter_order(self, client_order_index: int, new_price: Decimal):
        """Modify current Lighter order with new price."""
        try:
            if client_order_index is None:
                self.logger.error("❌ Cannot modify order - no order ID available")
                return

            lighter_price = round(float(new_price * self.price_multiplier))

            self.logger.info(f"🔧 Attempting to modify order - Market: {self.lighter_market_index}, "
                             f"Client Order Index: {client_order_index}, New Price: {lighter_price}")

            tx_info, tx_hash, error = await self.lighter_client.modify_order(
                market_index=self.lighter_market_index,
                order_index=client_order_index,
                base_amount=round(float(self.lighter_order_size * self.base_amount_multiplier)),
                price=lighter_price,
                trigger_price=0
            )

            if error is not None:
                self.logger.error(f"❌ Lighter order modification error: {error}")
                return

            self.lighter_order_price = new_price
            self.logger.info(f"🔄 Lighter order modified successfully: {self.lighter_order_side} "
                             f"{self.lighter_order_size} @ {new_price}")

        except Exception as e:
            self.logger.error(f"❌ Error modifying Lighter order: {e}")
            self.logger.error(f"❌ Full traceback: {traceback.format_exc()}")

    async def setup_backpack_websocket(self):
        """Setup Backpack websocket for order updates."""
        if not self.backpack_client:
            raise Exception("Backpack client not initialized")

        def order_update_handler(order_data):
            """Handle order updates from Backpack WebSocket."""
            if order_data.get('contract_id') != self.backpack_contract_id:
                return
            try:
                order_id = order_data.get('order_id')
                status = order_data.get('status')
                side = order_data.get('side', '').lower()
                filled_size = Decimal(order_data.get('filled_size', '0'))
                size = Decimal(order_data.get('size', '0'))
                price = order_data.get('price', '0')

                if side == 'buy':
                    order_type = "OPEN"
                else:
                    order_type = "CLOSE"

                if status == 'CANCELED' and filled_size > 0:
                    status = 'FILLED'

                # Handle the order update
                if status == 'FILLED' and self.backpack_order_status != 'FILLED':
                    trade_price = Decimal(price) if price else Decimal('0')
                    trade_value = filled_size * trade_price
                    if side == 'buy':
                        self.backpack_position += filled_size
                        # Track Backpack buy stats
                        self.bp_trade_count += 1
                        self.bp_buy_count += 1
                        self.bp_buy_volume_base += filled_size
                        self.bp_buy_cost_quote += trade_value
                    else:
                        self.backpack_position -= filled_size
                        # Track Backpack sell stats
                        self.bp_trade_count += 1
                        self.bp_sell_count += 1
                        self.bp_sell_volume_base += filled_size
                        self.bp_sell_revenue_quote += trade_value
                    self.logger.info(f"[{order_id}] [{order_type}] [Backpack] [{status}]: {filled_size} @ {price}")
                    self.backpack_order_status = status
                    if filled_size > Decimal('0.0001'):
                        self.log_trade_to_csv(
                            exchange='Backpack',
                            side=side,
                            price=str(price),
                            quantity=str(filled_size),
                            expected_price=str(self.exp_backpack_price)
                        )
                elif self.backpack_order_status != 'FILLED':
                    if status == 'OPEN':
                        self.logger.info(f"[{order_id}] [{order_type}] [Backpack] [{status}]: {size} @ {price}")
                    else:
                        self.logger.info(f"[{order_id}] [{order_type}] [Backpack] [{status}]: {filled_size} @ {price}")
                    self.backpack_order_status = status

            except Exception as e:
                self.logger.error(f"Error handling Backpack order update: {e}")

        try:
            self.backpack_client.setup_order_update_handler(order_update_handler)
            self.logger.info("✅ Backpack WebSocket order update handler set up")

            await self.backpack_client.connect()
            self.logger.info("✅ Backpack WebSocket connection established")

        except Exception as e:
            self.logger.error(f"Could not setup Backpack WebSocket handlers: {e}")

    def handle_backpack_order_book_update(self, message):
        """Handle Backpack order book updates from depth WebSocket."""
        try:
            if isinstance(message, str):
                message = json.loads(message)

            if message.get("stream") and "depth" in message.get("stream", ""):
                data = message.get("data", {})

                if data:
                    # Update bids - Backpack uses 'b' for bids
                    bids = data.get('b', [])
                    for bid in bids:
                        price = Decimal(bid[0])
                        size = Decimal(bid[1])
                        if size > 0:
                            self.backpack_order_book['bids'][price] = size
                        else:
                            self.backpack_order_book['bids'].pop(price, None)

                    # Update asks - Backpack uses 'a' for asks
                    asks = data.get('a', [])
                    for ask in asks:
                        price = Decimal(ask[0])
                        size = Decimal(ask[1])
                        if size > 0:
                            self.backpack_order_book['asks'][price] = size
                        else:
                            self.backpack_order_book['asks'].pop(price, None)

                    # Update best bid and ask with sizes
                    if self.backpack_order_book['bids']:
                        best_bid_price = max(self.backpack_order_book['bids'].keys())
                        self.backpack_best_bid = best_bid_price
                        self.backpack_best_bid_size = self.backpack_order_book['bids'][best_bid_price]
                    if self.backpack_order_book['asks']:
                        best_ask_price = min(self.backpack_order_book['asks'].keys())
                        self.backpack_best_ask = best_ask_price
                        self.backpack_best_ask_size = self.backpack_order_book['asks'][best_ask_price]

                    if not self.backpack_order_book_ready:
                        # Only mark as ready when BOTH sides have valid data
                        if (self.backpack_best_bid is not None and self.backpack_best_ask is not None
                                and self.backpack_best_bid > 0 and self.backpack_best_ask > 0
                                and self.backpack_best_bid < self.backpack_best_ask):
                            self.backpack_order_book_ready = True
                            self.logger.info(f"📊 Backpack order book ready - Best bid: {self.backpack_best_bid}, "
                                             f"Best ask: {self.backpack_best_ask}")
                        else:
                            self.logger.debug(f"📊 Backpack order book partial - Best bid: {self.backpack_best_bid}, "
                                              f"Best ask: {self.backpack_best_ask} (waiting for both sides)")

        except Exception as e:
            self.logger.error(f"Error handling Backpack order book update: {e}")
            self.logger.error(f"Message content: {message}")

    async def setup_backpack_depth_websocket(self):
        """Setup separate WebSocket connection for Backpack depth updates."""
        async def handle_depth_websocket():
            """Handle depth WebSocket connection."""
            url = "wss://ws.backpack.exchange"

            while not self.stop_flag:
                try:
                    async with websockets.connect(url) as ws:
                        # Subscribe to depth updates
                        subscribe_message = {
                            "method": "SUBSCRIBE",
                            "params": [f"depth.{self.backpack_contract_id}"]
                        }
                        await ws.send(json.dumps(subscribe_message))
                        self.logger.info(f"✅ Subscribed to Backpack depth updates for {self.backpack_contract_id}")

                        async for message in ws:
                            if self.stop_flag:
                                break

                            try:
                                if isinstance(message, bytes) and message == b'\x09':
                                    await ws.pong()
                                    continue

                                data = json.loads(message)

                                if data.get('stream') and 'depth' in data.get('stream', ''):
                                    self.handle_backpack_order_book_update(data)

                            except json.JSONDecodeError as e:
                                self.logger.warning(f"Failed to parse depth WebSocket message: {e}")
                            except Exception as e:
                                self.logger.error(f"Error handling depth WebSocket message: {e}")

                except websockets.exceptions.ConnectionClosed:
                    self.logger.warning("Backpack depth WebSocket connection closed, reconnecting...")
                except Exception as e:
                    self.logger.error(f"Backpack depth WebSocket error: {e}")

                if not self.stop_flag:
                    await asyncio.sleep(2)

        self.backpack_depth_ws_task = asyncio.create_task(handle_depth_websocket())
        self.logger.info("✅ Backpack depth WebSocket task started")

    async def get_lighter_position(self):
        """Get current Lighter position via REST API."""
        url = "https://mainnet.zklighter.elliot.ai/api/v1/account"
        headers = {"accept": "application/json"}

        current_position = None
        parameters = {"by": "index", "value": self.account_index}
        attempts = 0
        while current_position is None and attempts < 10:
            try:
                response = requests.get(url, headers=headers, params=parameters, timeout=10)
                response.raise_for_status()

                if not response.text.strip():
                    print("⚠️ Empty response from Lighter API for position check")
                    return self.lighter_position

                data = response.json()

                if 'accounts' not in data or not data['accounts']:
                    print(f"⚠️ Unexpected response format from Lighter API: {data}")
                    return self.lighter_position

                positions = data['accounts'][0].get('positions', [])
                for position in positions:
                    if position.get('symbol') == self.ticker:
                        current_position = Decimal(position['position']) * position['sign']
                        break
                if current_position is None:
                    current_position = 0

            except requests.exceptions.RequestException as e:
                print(f"⚠️ Network error getting position: {e}")
            except json.JSONDecodeError as e:
                print(f"⚠️ JSON parsing error in position response: {e}")
                print(f"Response text: {response.text[:200]}...")
            except Exception as e:
                print(f"⚠️ Unexpected error getting position: {e}")
            finally:
                attempts += 1
                await asyncio.sleep(1)

        if current_position is None:
            self.logger.error(f"❌ Failed to get Lighter position after {attempts} attempts")
            sys.exit(1)

        return current_position

    def get_backpack_balance(self) -> Decimal:
        """Get Backpack account net equity via GET /api/v1/capital/collateral.

        Response format (from API docs):
        {
            "assetsValue": "...",
            "borrowLiability": "...",
            "collateral": [...],
            "netEquity": "...",
            "netEquityAvailable": "...",
            "pnlUnrealized": "...",
            ...
        }
        """
        try:
            if self.backpack_client and hasattr(self.backpack_client, 'account_client'):
                collateral_data = self.backpack_client.account_client.get_collateral()
                if isinstance(collateral_data, dict):
                    # netEquity = total account value (assets - liabilities)
                    net_equity = collateral_data.get('netEquity')
                    if net_equity is not None:
                        return Decimal(str(net_equity))
                    # fallback: assetsValue
                    assets_value = collateral_data.get('assetsValue')
                    if assets_value is not None:
                        return Decimal(str(assets_value))
                self.logger.warning(f"⚠️ Unexpected BP collateral response type: {type(collateral_data)}, data: {str(collateral_data)[:200]}")
        except Exception as e:
            self.logger.warning(f"⚠️ Failed to get Backpack balance: {e}")
        return Decimal('-1')  # Indicates failure

    def get_lighter_balance(self) -> Decimal:
        """Get Lighter account equity (collateral + unrealized PnL) via GET /api/v1/account.

        Response format:
        {
            "code": 200,
            "accounts": [{
                "available_balance": "...",
                "collateral": "...",          // deposited margin only, does NOT include unrealized PnL
                "positions": [{
                    "unrealized_pnl": "...",   // per-position unrealized PnL
                    ...
                }],
                ...
            }]
        }

        Account equity = collateral + sum(unrealized_pnl of all positions)
        """
        try:
            url = f"{self.lighter_base_url}/api/v1/account"
            headers = {"accept": "application/json"}
            params = {"by": "index", "value": self.account_index}
            response = requests.get(url, headers=headers, params=params, timeout=10)
            response.raise_for_status()
            data = response.json()
            if 'accounts' in data and data['accounts']:
                account = data['accounts'][0]
                # collateral = deposited margin (does NOT include unrealized PnL)
                collateral_str = account.get('collateral')
                if collateral_str is None:
                    collateral_str = account.get('available_balance', '0')
                collateral = Decimal(str(collateral_str))

                # Add unrealized PnL from all positions to get true account equity
                total_unrealized_pnl = Decimal('0')
                positions = account.get('positions', [])
                for pos in positions:
                    pnl = pos.get('unrealized_pnl', '0')
                    total_unrealized_pnl += Decimal(str(pnl))

                equity = collateral + total_unrealized_pnl
                return equity
        except Exception as e:
            self.logger.warning(f"⚠️ Failed to get Lighter balance: {e}")
        return Decimal('-1')  # Indicates failure

    async def check_position_balance(self, log_position: bool = True) -> bool:
        """Check if positions on both exchanges are balanced. If not, auto-rebalance."""
        attempts = 0
        position_is_balanced = False
        while attempts < 4:
            attempts += 1
            self.lighter_position = await self.get_lighter_position()
            self.backpack_position = await self.get_backpack_position()
            if log_position:
                self.logger.info(f"Backpack position: {self.backpack_position} | Lighter position: {self.lighter_position}")

            imbalance = self.backpack_position + self.lighter_position
            if abs(imbalance) > self.order_quantity:
                self.logger.warning(f"⚠️ Attempt {attempts} | Position imbalance: {imbalance}")
                # Auto-rebalance: reduce the side with the larger absolute position
                await self.rebalance_positions(imbalance)
                await asyncio.sleep(5)
            else:
                position_is_balanced = True
                break
        return position_is_balanced

    async def rebalance_positions(self, imbalance: Decimal):
        """Auto-rebalance positions between Backpack and Lighter.

        imbalance = backpack_position + lighter_position
        If imbalance > 0: net long exposure, need to sell on the exchange with larger long position
        If imbalance < 0: net short exposure, need to buy on the exchange with larger short position

        Strategy: adjust the exchange with the LARGER absolute position toward balance.
        """
        rebalance_qty = abs(imbalance)
        # Round to Lighter's size step to avoid precision issues
        if hasattr(self, 'lighter_size_step') and self.lighter_size_step:
            rebalance_qty = (rebalance_qty / self.lighter_size_step).to_integral_value() * self.lighter_size_step
        if rebalance_qty <= 0:
            self.logger.warning(f"⚠️ Rebalance qty too small after rounding: {abs(imbalance)} → {rebalance_qty}")
            return
        self.logger.info(f"🔄 Auto-rebalancing: imbalance = {imbalance}, rebalance_qty = {rebalance_qty}")

        try:
            if imbalance > 0:
                # Net long: we need to sell somewhere or buy somewhere
                # If backpack is more long than lighter is short, sell on backpack
                # If lighter is less short than backpack is long, sell on lighter
                if abs(self.backpack_position) >= abs(self.lighter_position):
                    self.logger.info(f"🔄 Selling {rebalance_qty} on Backpack to rebalance")
                    await self.place_backpack_market_order('sell', rebalance_qty)
                    await asyncio.sleep(2)
                else:
                    self.logger.info(f"🔄 Selling {rebalance_qty} on Lighter to rebalance")
                    await self.place_lighter_market_order('sell', rebalance_qty)
                    await asyncio.sleep(2)
            else:
                # Net short: we need to buy somewhere
                if abs(self.backpack_position) >= abs(self.lighter_position):
                    self.logger.info(f"🔄 Buying {rebalance_qty} on Backpack to rebalance")
                    await self.place_backpack_market_order('buy', rebalance_qty)
                    await asyncio.sleep(2)
                else:
                    self.logger.info(f"🔄 Buying {rebalance_qty} on Lighter to rebalance")
                    await self.place_lighter_market_order('buy', rebalance_qty)
                    await asyncio.sleep(2)

            self.logger.info(f"✅ Rebalance order placed, waiting for confirmation...")
        except Exception as e:
            self.logger.error(f"❌ Error during rebalancing: {e}")
            self.logger.error(f"❌ Full traceback: {traceback.format_exc()}")

    async def trading_loop(self):
        """Main trading loop implementing the v2 statistical arbitrage strategy.

        Strategy:
        1. Collect spread history (lighter_best_bid - backpack_best_bid)
        2. After 1000+ data points, compute the median spread
        3. Set dynamic thresholds: median ± (ask_price × 0.0002)
        4. When spread exceeds threshold, place simultaneous market orders on both exchanges
        """
        self.logger.info(f"🚀 Starting hedge bot v2 for {self.ticker}")

        # Initialize clients
        try:
            self.initialize_lighter_client()
            self.initialize_backpack_client()

            # Get contract info
            self.backpack_contract_id, self.backpack_tick_size = await self.get_backpack_contract_info()
            self.lighter_market_index, self.base_amount_multiplier, self.price_multiplier, self.tick_size = self.get_lighter_market_config()

            self.logger.info(f"Contract info loaded - Backpack: {self.backpack_contract_id}, "
                             f"Lighter: {self.lighter_market_index}")

        except Exception as e:
            self.logger.error(f"❌ Failed to initialize: {e}")
            return

        # Setup Backpack websocket for order updates
        try:
            await self.setup_backpack_websocket()
            self.logger.info("✅ Backpack WebSocket connection established for order updates")

        except Exception as e:
            self.logger.error(f"❌ Failed to setup Backpack websocket: {e}")
            return

        # Setup Backpack depth websocket for order book
        try:
            await self.setup_backpack_depth_websocket()

            # Wait for initial Backpack order book data with timeout
            self.logger.info("⏳ Waiting for initial Backpack order book data...")
            timeout = 10  # seconds
            start_time = time.time()
            while not self.backpack_order_book_ready and not self.stop_flag:
                if time.time() - start_time > timeout:
                    self.logger.warning(f"⚠️ Timeout waiting for Backpack WebSocket order book data after {timeout}s")
                    break
                await asyncio.sleep(0.5)

            if self.backpack_order_book_ready:
                self.logger.info("✅ Backpack WebSocket order book data received")
            else:
                self.logger.warning("⚠️ Backpack WebSocket order book not ready")

        except Exception as e:
            self.logger.error(f"❌ Failed to setup Backpack depth websocket: {e}")
            return

        # Setup Lighter websocket
        try:
            self.lighter_ws_task = asyncio.create_task(self.handle_lighter_ws())
            self.logger.info("✅ Lighter WebSocket task started")

            # Wait for initial Lighter order book data with timeout
            self.logger.info("⏳ Waiting for initial Lighter order book data...")
            timeout = 10  # seconds
            start_time = time.time()
            while not self.lighter_order_book_ready and not self.stop_flag:
                if time.time() - start_time > timeout:
                    self.logger.warning(f"⚠️ Timeout waiting for Lighter WebSocket order book data after {timeout}s")
                    break
                await asyncio.sleep(0.5)

            if self.lighter_order_book_ready:
                self.logger.info("✅ Lighter WebSocket order book data received")
            else:
                self.logger.warning("⚠️ Lighter WebSocket order book not ready")

        except Exception as e:
            self.logger.error(f"❌ Failed to setup Lighter websocket: {e}")
            return

        await asyncio.sleep(5)

        last_position_log = time.time()
        while not self.stop_flag:
            if time.time() - last_position_log > 10:
                log_position = True
                last_position_log = time.time()
            else:
                log_position = False

            position_is_balanced = await self.check_position_balance(log_position)
            if not position_is_balanced:
                self.logger.warning("⚠️ Position rebalancing failed after 4 attempts, retrying next cycle...")
                await asyncio.sleep(10)
                continue

            if None in [self.lighter_best_bid, self.lighter_best_ask, self.backpack_best_bid, self.backpack_best_ask]:
                await asyncio.sleep(1)
                continue

            # Record spread using mid prices for symmetry between long/short directions
            # Using bid-only spread causes asymmetry: reducing position requires overcoming
            # Lighter's wider bid-ask spread, making it structurally harder to trigger.
            lighter_mid = (self.lighter_best_bid + self.lighter_best_ask) / 2
            bp_mid = (self.backpack_best_bid + self.backpack_best_ask) / 2
            self.spread_history.append(lighter_mid - bp_mid)

            if len(self.spread_history) > 200:
                data = list(self.spread_history)
                median_val = statistics.median(data)
                long_bp_threshold = median_val + self.backpack_best_ask * Decimal("0.0002")
                short_bp_threshold = -(median_val - self.backpack_best_ask * Decimal("0.0002"))
                # Log thresholds to JSON file
                self.log_thresholds_to_json(long_bp_threshold, short_bp_threshold)
            else:
                if log_position:
                    self.logger.info(f"logging spread history. {len(self.spread_history)}/200")
                    self.logger.info(f"best bid: {self.lighter_best_bid} | best ask: {self.lighter_best_ask}")
                await asyncio.sleep(1)
                continue

            long_bp = False
            short_bp = False

            # --- Max position threshold relaxation logic ---
            # When position is at max, gradually relax the threshold for the
            # direction that would REDUCE position, so the bot doesn't stay idle.
            at_long_max = self.max_position > 0 and self.backpack_position >= self.max_position
            at_short_max = self.max_position > 0 and self.backpack_position <= -1 * self.max_position
            at_max = at_long_max or at_short_max

            if at_max:
                if self.at_max_position_since is None:
                    self.at_max_position_since = time.time()
                    self.logger.info(f"⏱️ Position hit max ({self.backpack_position}), starting relaxation timer")
            else:
                if self.at_max_position_since is not None:
                    self.logger.info(f"✅ Position back within limits ({self.backpack_position}), resetting relaxation timer")
                self.at_max_position_since = None

            threshold_relaxation = Decimal('0')
            if self.at_max_position_since is not None:
                seconds_at_max = Decimal(str(time.time() - self.at_max_position_since))
                if seconds_at_max > self.threshold_relax_start:
                    relax_seconds = seconds_at_max - self.threshold_relax_start
                    ref_price = self.backpack_best_ask if self.backpack_best_ask else Decimal('1')
                    threshold_relaxation = min(
                        relax_seconds * self.threshold_relax_rate,
                        ref_price * self.threshold_relax_cap
                    )
                    if log_position:
                        self.logger.info(
                            f"🔓 Threshold relaxation active: {float(threshold_relaxation):.4f} "
                            f"(at max for {float(seconds_at_max):.0f}s, "
                            f"cap={float(ref_price * self.threshold_relax_cap):.4f})")

            # Apply relaxation: only relax the direction that REDUCES position
            effective_long_threshold = long_bp_threshold
            effective_short_threshold = short_bp_threshold
            if at_short_max:
                # Need to go long (buy BP) to reduce short position
                effective_long_threshold = long_bp_threshold - threshold_relaxation
            if at_long_max:
                # Need to go short (sell BP) to reduce long position
                effective_short_threshold = short_bp_threshold - threshold_relaxation

            # Determine which directions are allowed based on position limits
            # When at max long, ONLY allow short (reduce); when at max short, ONLY allow long (reduce)
            allow_long = not at_long_max   # Can't go more long if already at max long
            allow_short = not at_short_max  # Can't go more short if already at max short

            # Long Backpack signal: lighter_bid - backpack_ask > threshold
            # (buy on Backpack, sell on Lighter) → increases BP position
            long_signal = (self.lighter_best_bid and self.backpack_best_ask and
                    self.lighter_best_bid - self.backpack_best_ask > effective_long_threshold)
            # Short Backpack signal: backpack_bid - lighter_ask > threshold
            # (sell on Backpack, buy on Lighter) → decreases BP position
            short_signal = (self.backpack_best_bid and self.lighter_best_ask and
                    self.backpack_best_bid - self.lighter_best_ask > effective_short_threshold)

            # When at max position, prioritize the REDUCING direction
            if at_long_max and short_signal:
                # At max long → MUST reduce first, prioritize short even if long signal also fires
                self.exp_backpack_price = self.backpack_best_bid
                self.exp_lighter_price = self.lighter_best_ask
                short_bp = True
            elif at_short_max and long_signal:
                # At max short → MUST reduce first, prioritize long even if short signal also fires
                self.exp_backpack_price = self.backpack_best_ask
                self.exp_lighter_price = self.lighter_best_bid
                long_bp = True
            elif long_signal and allow_long:
                self.exp_backpack_price = self.backpack_best_ask
                self.exp_lighter_price = self.lighter_best_bid
                long_bp = True
            elif short_signal and allow_short:
                self.exp_backpack_price = self.backpack_best_bid
                self.exp_lighter_price = self.lighter_best_ask
                short_bp = True

            if long_bp:
                order_quantity = min(self.order_quantity, self.backpack_best_ask_size)

                try:
                    # Place both trades concurrently
                    await asyncio.gather(
                        self.place_backpack_market_order('buy', order_quantity),
                        self.place_lighter_market_order('sell', order_quantity)
                    )
                except Exception as e:
                    self.logger.error(f"⚠️ Error in trading loop: {e}")
                    self.logger.error(f"⚠️ Full traceback: {traceback.format_exc()}")

            elif short_bp:
                order_quantity = min(self.order_quantity, self.backpack_best_bid_size)

                try:
                    # Place both trades concurrently
                    await asyncio.gather(
                        self.place_backpack_market_order('sell', order_quantity),
                        self.place_lighter_market_order('buy', order_quantity)
                    )
                except Exception as e:
                    self.logger.error(f"⚠️ Error in trading loop: {e}")
                    self.logger.error(f"⚠️ Full traceback: {traceback.format_exc()}")

            else:
                await asyncio.sleep(1)

            # Periodic summary output
            self.print_periodic_summary()

    async def run(self):
        """Run the hedge bot."""
        self.setup_signal_handlers()

        try:
            await self.trading_loop()
        except KeyboardInterrupt:
            self.logger.info("\n🛑 Received interrupt signal...")
        except Exception as e:
            self.logger.error(f"Error in trading loop: {e}")
            self.logger.error(f"Full traceback: {traceback.format_exc()}")
        finally:
            # Print final summary before shutdown
            self.print_periodic_summary(force=True)
            self.logger.info("🔄 Cleaning up...")
            try:
                await self.async_shutdown()
            except Exception as e:
                pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Backpack-Lighter Hedge Bot V2 (Statistical Arbitrage)")
    parser.add_argument("--ticker", type=str, required=True, help="Trading pair ticker (e.g., BTC, ETH, SOL)")
    parser.add_argument("--quantity", type=str, required=True, help="Order quantity per trade")
    parser.add_argument("--max-position", type=str, default="0", help="Maximum position size (0 = no limit)")
    parser.add_argument("--fill-timeout", type=int, default=5, help="Fill timeout in seconds")
    parser.add_argument("--env-file", type=str, default=".env", help="Path to .env file (default: .env)")
    parser.add_argument("--summary-interval", type=int, default=300, help="Periodic summary interval in seconds (default: 300)")
    parser.add_argument("--relax-start", type=int, default=60, help="Seconds at max position before threshold relaxation starts (default: 60)")
    parser.add_argument("--relax-rate", type=str, default="0.00002", help="Threshold relaxation per second (default: 0.00002)")
    parser.add_argument("--relax-cap", type=str, default="0.001", help="Max threshold relaxation as fraction of price (default: 0.001)")

    args = parser.parse_args()

    # Load environment variables from .env file
    dotenv.load_dotenv(args.env_file)

    order_quantity = Decimal(args.quantity)
    max_position = Decimal(args.max_position)

    bot = HedgeBot(
        ticker=args.ticker,
        order_quantity=order_quantity,
        fill_timeout=args.fill_timeout,
        max_position=max_position
    )
    bot.summary_interval = args.summary_interval
    bot.threshold_relax_start = args.relax_start
    bot.threshold_relax_rate = Decimal(args.relax_rate)
    bot.threshold_relax_cap = Decimal(args.relax_cap)

    asyncio.run(bot.run())
