"""
Train custom NLP model for test case generation
"""
import logging
import json
from pathlib import Path
from typing import Dict, List
import torch # type: ignore
from transformers import (
    AutoTokenizer, AutoModelForSeq2SeqLM,
    TrainingArguments, Trainer, DataCollatorForSeq2Seq
)
from datasets import Dataset # type: ignore
import evaluate # type: ignore
import numpy as np # type: ignore

from config_Phase3 import ModelPaths # type: ignore

logger = logging.getLogger(__name__)

class TestGenerationTrainer:
    """Train custom model for test case generation"""
    
    def __init__(self, model_name: str = "t5-small"):
        self.model_name = model_name
        self.tokenizer = None
        self.model = None
        self.trainer = None
        
        self._setup_model()
    
    def _setup_model(self):
        """Setup model and tokenizer"""
        try:
            self.tokenizer = AutoTokenizer.from_pretrained(self.model_name)
            self.model = AutoModelForSeq2SeqLM.from_pretrained(self.model_name)
            
            # Add special tokens if needed
            special_tokens = ["<SPEC>", "<TEST>", "<FUNC>", "<DOMAIN>"]
            self.tokenizer.add_tokens(special_tokens)
            self.model.resize_token_embeddings(len(self.tokenizer))
            
            logger.info(f"✅ Model {self.model_name} loaded successfully")
            
        except Exception as e:
            logger.error(f"Model setup failed: {e}")
            raise
    
    def prepare_training_data(self, data_path: Path) -> Dataset:
        """Prepare training data from JSON files"""
        
        # Load training data
        with open(data_path / "train_data.json", "r") as f:
            train_data = json.load(f)
        
        # Convert to training format
        training_examples = []
        
        for example in train_data:
            # Create input-output pairs
            spec = example["specification"]
            domain = example.get("domain", "general")
            function_sig = example.get("function_signature", "")
            
            # Create input prompt
            input_text = f"<SPEC> {spec} <DOMAIN> {domain} <FUNC> {function_sig}"
            
            # Create target (all test cases joined)
            target_text = " <TEST> ".join(example["test_cases"])
            
            training_examples.append({
                "input_text": input_text,
                "target_text": target_text
            })
        
        return Dataset.from_list(training_examples)
    
    def tokenize_data(self, dataset: Dataset, max_length: int = 512) -> Dataset:
        """Tokenize the dataset"""
        
        def tokenize_function(examples):
            # Tokenize inputs
            model_inputs = self.tokenizer(
                examples["input_text"],
                max_length=max_length,
                truncation=True,
                padding=False
            )
            
            # Tokenize targets
            targets = self.tokenizer(
                examples["target_text"],
                max_length=max_length,
                truncation=True,
                padding=False
            )
            
            model_inputs["labels"] = targets["input_ids"]
            return model_inputs
        
        return dataset.map(tokenize_function, batched=True)
    
    def train_model(
        self, 
        train_dataset: Dataset,
        val_dataset: Dataset = None,
        output_dir: str = "models/fine-tuned-test-generator",
        num_epochs: int = 3
    ):
        """Train the model"""
        
        # Setup training arguments
        training_args = TrainingArguments(
            output_dir=output_dir,
            num_train_epochs=num_epochs,
            per_device_train_batch_size=4,
            per_device_eval_batch_size=4,
            warmup_steps=500,
            weight_decay=0.01,
            logging_dir=f"{output_dir}/logs",
            logging_steps=100,
            evaluation_strategy="steps" if val_dataset else "no",
            eval_steps=500 if val_dataset else None,
            save_steps=1000,
            save_total_limit=2,
            load_best_model_at_end=True if val_dataset else False,
            metric_for_best_model="eval_loss" if val_dataset else None,
            report_to=None  # Disable wandb/tensorboard
        )
        
        # Data collator
        data_collator = DataCollatorForSeq2Seq(
            tokenizer=self.tokenizer,
            model=self.model,
            padding=True
        )
        
        # Initialize trainer
        self.trainer = Trainer(
            model=self.model,
            args=training_args,
            train_dataset=train_dataset,
            eval_dataset=val_dataset,
            tokenizer=self.tokenizer,
            data_collator=data_collator
        )
        
        # Start training
        logger.info("🚀 Starting model training...")
        self.trainer.train()
        
        # Save the final model
        self.trainer.save_model(output_dir)
        self.tokenizer.save_pretrained(output_dir)
        
        logger.info(f"✅ Model training complete. Saved to {output_dir}")

def run_training():
    """Run the training process"""
    
    # Generate training data first
    from data.training.generate_training_data import generate_training_dataset
    
    logger.info("📊 Generating training data...")
    generate_training_dataset("data/training", 1000)
    
    # Initialize trainer
    trainer = TestGenerationTrainer()
    
    # Prepare datasets
    train_dataset = trainer.prepare_training_data(Path("data/training"))
    train_dataset = trainer.tokenize_data(train_dataset)
    
    # Split for validation
    train_val_split = train_dataset.train_test_split(test_size=0.1)
    train_ds = train_val_split["train"]
    val_ds = train_val_split["test"]
    
    # Train the model
    trainer.train_model(train_ds, val_ds, num_epochs=2)
    
    logger.info("🎉 Training pipeline complete!")

if __name__ == "__main__":
    run_training()
